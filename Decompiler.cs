namespace KismetAnalyzer;

using System.Text.RegularExpressions;

using UAssetAPI;
using UAssetAPI.UnrealTypes;
using UAssetAPI.ExportTypes;
using UAssetAPI.Kismet.Bytecode;
using UAssetAPI.Kismet.Bytecode.Expressions;

using Dot;
using Xunit;
using System.Collections.Generic;
using System.Linq;
using System.Collections;
using static KismetAnalyzer.SummaryGenerator;
using System.Text;
using UAssetAPI.FieldTypes;
using Newtonsoft.Json.Linq;
using System.Security.Cryptography;
using System.Runtime.ExceptionServices;
using System;
using static KismetAnalyzer.Decompiler;
using System.Data.SqlTypes;
using System.Xml.Linq;
using static System.Net.Mime.MediaTypeNames;

public class Decompiler {

    static public string gFunctionName = "(none)";

    static string getnparameter(int n, int start)
    {
        string[] parameters = new string[n];
        for (int i = 0; i < n; i++)
        {
            parameters[i] = $"{{{start + i}}}";
        }
        return string.Join(", ", parameters);
    }
    static string getnpairparameter(int n, int start)
    {
        string[] parameters = new string[n];
        for (int i = 0; i < n; i++)
        {
            parameters[i] = $"{{{start + i * 2}}}: {{{start + i * 2 + 1}}}";
        }
        return string.Join(", ", parameters);
    }
    class Result
    {
        public bool success;
        public T Unwrap<T>()
        {
            // cast to Ok<T> and get value
            if (this is _Ok<T> ok)
            {
                return ok.value;
            }
            else
            {
                throw new Exception("Unwrap failed");
            }
        }
        public bool IsOk()
        {
            return success;
        }

    }
    class _Ok<T> : Result
    {
        public T value;
        public _Ok(T value)
        {
            this.value = value;
            success = true;
        }
    }

    static Result Ok<T>(T value)
    {
        return new _Ok<T>(value);
    }


    class Error : Result
    {
        public string message;
        public Error(string message)
        {
            this.message = message;
            success = false;
        }
    }

    static Result Err(string message)
    {
        return new Error(message);
    }
    public class FormatableCodes
    {
        public string format;
        public object[] codes;

        public FormatableCodes(string format, params object[] codes)
        {
            this.format = format;
            this.codes = codes;
        }
        public override string ToString()
        {
            if (codes != null && codes.Length > 0)
            {
                try
                {
                    return string.Format(format, codes);

                } catch (FormatException e)
                {
                    Console.Error.WriteLine("ERROR: FormatableCodes.ToString() failed: " + e.Message);
                    return $"<<<!!!!! {e.Message} !!!! {format} !!!!! {codes}>>>";
                }
            }
            else
            {
                return format;
            }
        }
    }

    public FormatableCodes Codes(string format, params object[] codes)
    {
        return new FormatableCodes(format, codes);
    }
    public class ASTNode : ICloneable
    {
        public uint line, idx;
        public FormatableCodes code;
        public bool noped;
        public ASTNode(uint line, FormatableCodes code)
        {
            this.line = line;
            this.code = code;
        }

        public override string ToString()
        {
            return code.ToString();
        }

        virtual public void RenameIdx(Dictionary<uint, uint> addressRename)
        {
            if (addressRename.ContainsKey(line))
            {
                idx = addressRename[line];
            }
        }

        public void nop()
        {
            code.format = "// " + code.format;
            noped = true;
        }

        #region ICloneable Members

        public object Clone()
        {
            return this.MemberwiseClone();
        }

        #endregion

    }


    public class LetNode : ASTNode
    {
        public readonly bool variable_by_ast;
        public readonly ASTNode? variable;
        public readonly string? variable_str;
        public readonly ASTNode expression;
        public readonly string type;

        static public FormatableCodes let_code(ASTNode variable, ASTNode expression, string type)
        {
            if (type != "")
            {
                return new FormatableCodes($"let {{0}} : {type} = {{1}}", variable, expression);
            } else
            {
                return new FormatableCodes($"let {{0}} = {{1}}", variable, expression);
            }
        }

        static public FormatableCodes let_code(string variable, ASTNode expression, string type)
        {
            if (type != "")
            {
                return new FormatableCodes($"let {{0}} : {type} = {{1}}", variable, expression);
            }
            else
            {
                return new FormatableCodes($"let {{0}} = {{1}}", variable, expression);
            }
        }

        public LetNode(uint line, ASTNode variable, ASTNode expression, string type = "") : base(line, let_code(variable, expression, type))
        {
            this.variable = variable;
            this.expression = expression;
            this.type = type;
            variable_by_ast = true;
        }

        public LetNode(uint line, string variable, ASTNode expression, string type = "") : base(line, let_code(variable, expression, type))
        {
            variable_str = variable;
            this.expression = expression;
            this.type = type;
            variable_by_ast = false;
        }

        public string GetVariable()
        {
            if (variable_by_ast)
            {
                return variable.ToString();
            }
            else
            {
                return variable_str;
            }
        }
    }

    public class CallNode : ASTNode
    {
        public readonly string func;
        public readonly ASTNode[] args;
        public readonly string prefix;

        static FormatableCodes call_code(ASTNode func, ASTNode[] args, string prefix)
        {
            return new FormatableCodes($"{prefix}{{0}}({getnparameter(args.Length, 1)})", func, args);
        }

        static FormatableCodes call_code(string func, ASTNode[] args, string prefix)
        {
            return new FormatableCodes($"{prefix}{func}({getnparameter(args.Length, 0)})", args);
        }
        public CallNode(uint line, ASTNode func, ASTNode[] args, string prefix) : base(line, call_code(func, args, prefix))
        {
            this.func = func.ToString();
            this.args = args;
            this.prefix = prefix;
        }

        public CallNode(uint line, string func, ASTNode[] args, string prefix): base(line, call_code(func, args, prefix))
        {
            this.func = func;
            this.args = args;
            this.prefix = prefix;
        }
    }

    public class ControlFlowNode : ASTNode
    {
        public ControlFlowNode(uint line, FormatableCodes code) : base(line, code)
        {
        }
    }

    public class ReturnNode : ControlFlowNode
    {
        public ReturnNode(uint line, ASTNode value) : base(line, new FormatableCodes("return {0}", value))
        {
        }
    }


    public class IfNode : ControlFlowNode
    {
        public int true_branch;
        public int false_branch;
        public readonly ASTNode cond;

        static FormatableCodes if_code(ASTNode cond)
        {
            return new FormatableCodes("if ({0})", cond);
        }

        public IfNode(uint line, ASTNode cond, int true_branch, int false_branch) : base(line, if_code(cond))
        {
            this.true_branch = true_branch;
            this.false_branch = false_branch;
            this.cond = cond;
        }

        public override void RenameIdx(Dictionary<uint, uint> addressRename)
        {
            // rename true_branch and false_branch
            if (addressRename.ContainsKey((uint) true_branch))
            {
                true_branch = (int)addressRename[(uint) true_branch];
            }
            if (addressRename.ContainsKey((uint) false_branch))
            {
                false_branch = (int)addressRename[(uint) false_branch];
            }
            base.RenameIdx(addressRename);
        }

    }


    public class GotoNode : ControlFlowNode
    {
        public int jump;
        public GotoNode(uint line, int jump) : base(line, new FormatableCodes("$goto .L{0}", jump))
        {
            this.jump = jump;
        }

        public override void RenameIdx(Dictionary<uint, uint> addressRename)
        {
            if (addressRename.ContainsKey((uint) jump))
            {
                jump = (int)addressRename[(uint) jump];
            }
            code = new FormatableCodes("$goto .L{0}", jump);
            base.RenameIdx(addressRename);
        }
    }
    public class GotoComputeNode : ControlFlowNode
    {
        public readonly ASTNode jump;
        // no need to rename:
        public List<uint> resolved_jumps;
        public GotoComputeNode(uint line, ASTNode jump) : base(line, new FormatableCodes("$goto_compute .L{0}", jump))
        {
            this.jump = jump;
            resolved_jumps = new List<uint>();
        }
    }

    public class IfNotNode : ASTNode
    {
        public int false_branch;
        public readonly ASTNode cond;

        static FormatableCodes if_code(ASTNode cond, int false_branch)
        {
            return new FormatableCodes("if !({0}) goto .L{1}", cond, false_branch);
        }

        public IfNotNode(uint line, ASTNode cond, int false_branch) : base(line, if_code(cond, false_branch))
        {
            this.cond = cond;
            this.false_branch = false_branch;
        }

        public IfNode ToIfNode(int true_branch)
        {
            return new IfNode(line, cond, true_branch, false_branch);
        }

        public override void RenameIdx(Dictionary<uint, uint> addressRename)
        {
            if (addressRename.ContainsKey((uint) false_branch))
            {
                false_branch = (int)addressRename[(uint) false_branch];
            }
            base.RenameIdx(addressRename);
        }
    }
    public class EndOfThreadNode : ASTNode
    {
        public EndOfThreadNode(uint line) : base(line, new FormatableCodes("$pop()"))
        {
        }
    }

    public class EndOfThreadIfNotNode : ASTNode
    {
        public readonly ASTNode cond;
        public EndOfThreadIfNotNode(uint line, ASTNode cond) : base(line, new FormatableCodes("if !({0}) goto $pop()", cond))
        {
            this.cond = cond;
        }

        public EndOfThreadIfNode ToIfNode(int true_branch)
        {
            return new EndOfThreadIfNode(line, cond, true_branch);
        }
    }

    public class EndOfThreadIfNode : ASTNode
    {
        public readonly ASTNode cond;
        public int true_branch;
        public EndOfThreadIfNode(uint line, ASTNode cond, int true_branch) : base(line, new FormatableCodes("if !({0}) goto $pop()", cond))
        {
            this.cond = cond;
            this.true_branch = true_branch;
        }

        public override void RenameIdx(Dictionary<uint, uint> addressRename)
        {
            if (addressRename.ContainsKey((uint) true_branch))
            {
                true_branch = (int) addressRename[(uint) true_branch];
            }
            base.RenameIdx(addressRename);
        }
    }

    public class PushFlowNode : ASTNode
    {
        public uint target;
        public PushFlowNode(uint line, uint target) : base(line, new FormatableCodes("$push(.LP{0})", target))
        { 
            this.target = target;
        }

        public override void RenameIdx(Dictionary<uint, uint> addressRename)
        {
            if (addressRename.ContainsKey(target))
            {
                target = addressRename[target];
            }
            code = new FormatableCodes("$push(.LP{0})", target);
            base.RenameIdx(addressRename);
        }
    }

    public ASTNode Line(uint line, FormatableCodes code)
    { 
        return new ASTNode(line, code);
    }

    public ASTNode IfNot(uint line, ASTNode code, int false_branch)
    {
        return new IfNotNode(line, code, false_branch);
    }

    public ASTNode Goto(uint line, int jump)
    {
        return new GotoNode(line, jump);
    }

    public class BasicBlock
    {
        public uint idx;
        public uint line_start, line_end;
        public ASTNode[] nodes;
        public BasicBlock? next;
        public uint resolving_next;
        public bool generated;
        public BasicBlock(ASTNode[] nodes)
        {
            this.nodes = nodes;
            next = null;
            resolving_next = 0x7fffffff;
        }
        public override string ToString()
        {
            return string.Join("\n", nodes.Select(x => x.ToString()));
        }
        virtual public void ResolveFlow(BasicBlock block)
        {
            uint target = block.idx;
            if (target == resolving_next)
            {
                next = block;
            }
        }

        virtual public void UpdateFlow(BasicBlock block)
        {
            if (next != null)
            {
                if (next.idx == block.idx)
                {
                    next = block;
                }
            }
        }

        // callback function
        virtual public void ForEachNext(Func<BasicBlock, bool> callback)
        {
            if (next != null)
            {
                callback(next);
            }
        }

        virtual public void QuickNext(Func<BasicBlock, bool> callback)
        {
            if (next != null)
            {
                callback(next);
            }
        }

        virtual public bool IsNodeDiverge()
        {
            return false;
        }

        public void GenerateNextCode(BasicBlock vnext, StringBuilder output, BasicBlock terminate, int ident, BasicBlock continueb, BasicBlock breakb, BasicBlock parent_next, string ident_str)
        {
            if (vnext != null)
            {

                if (vnext == continueb)
                {
                    if (continueb != parent_next)
                        output.Append($"{ident_str}continue;\n");
                }
                else
                {
                    if (vnext == breakb)
                    {
                        if (breakb != parent_next)
                            output.Append($"{ident_str}break;\n");
                    }
                    else
                    {
                        if (vnext != terminate)
                        {
                            if (vnext.generated)
                            {
                                if (vnext != parent_next)
                                    output.Append($"{ident_str}goto .L{vnext.idx};\n");
                            }
                            else
                            {
                                output.Append($"{ident_str}.L{vnext.idx}:\n");
                                //if (terminate != null)
                                //    output.Append($"Terminate = {terminate.idx}");
                                vnext.GenerateCode(output, terminate, continueb, breakb, parent_next, ident);
                            }
                        }
                            
                    }
                }
            }
        }

        public string GenerateNodeCode(string ident_str)
        {
            return string.Join("\n", nodes.Where((x) => !x.noped).Select(x => ident_str + x.ToString()));
        }

        virtual public void GenerateCode(StringBuilder output /* IO */, BasicBlock terminate /* where to stop generate */, BasicBlock continueb /* where to go when continue */, BasicBlock breakb /* where to go when break */, BasicBlock parent_next /* where to go when pass } */, int ident)
        {
            generated = true;
            var ident_str = new string('\t', ident);
            output.Append(GenerateNodeCode(ident_str) + "\n");
            GenerateNextCode(next, output, terminate, ident, continueb, breakb, parent_next, ident_str);
        }


        public void GenerateSwitchLike(StringBuilder output, BasicBlock[] cases, string[] switch_exp, BasicBlock continueb, string switch_name, string cond_str, int ident)
        {
            var ident_str = new string('\t', ident);
            var ident_str_1 = new string('\t', ident + 1);
            var ident_str_2 = new string('\t', ident + 2);
            output.Append($"{ident_str}{switch_name} ({cond_str}) {{\n");
            var merged = new Dictionary<BasicBlock, List<string>>();
            if (switch_exp == null)
            {
                switch_exp = new string[cases.Length];
                for (int i = 0; i < cases.Length; i++)
                {
                    switch_exp[i] = cases[i].line_start.ToString();
                }
            }
            for (int i = 0; i < cases.Length; i++)
            {
                if (cases[i] != null)
                {
                    var real_next = cases[i];
                    if (cases[i] is GoToBasicBlock gbb && gbb.nodes.Length == 0 && gbb.next != null)
                    {
                        real_next = cases[i].next;
                    }
                    if (!merged.ContainsKey(real_next))
                    {
                        merged[real_next] = new List<string>();
                    }
                    merged[real_next].Add(switch_exp[i]);
                }
            }
            
            foreach (var kv in merged)
            {
                output.Append(string.Join("\n", kv.Value.Select((x) => $"{ident_str_1}case {x}:")) + "{\n");
                GenerateNextCode(kv.Key, output, next, ident + 2, continueb, next, null, ident_str_2);
                output.Append($"{ident_str_1}}}\n");
            }

            output.Append($"{ident_str}}}\n");
        }
    }

    public enum SwitchType
    {
        Unknown, Integer, String, Enum, Name
    }

    public class IfOrLoopOrSwitchBasicBlock : BasicBlock
    {
        public readonly ASTNode cond;
        public BasicBlock? true_branch, false_branch;
        public uint resolving_true_branch, resolving_false_branch;
        public bool no_next_if;

        public bool is_loop;
        public bool is_do_loop;
        public BasicBlock? continue_block, loop_body;

        public bool is_switch;
        public BasicBlock[]? cases_body;
        public ASTNode[]? expressions;
        public ASTNode? value;
        public SwitchType switch_type; // Integer, String, Enum, Name

        public IfOrLoopOrSwitchBasicBlock(ASTNode[] nodes, ASTNode cond, uint true_branch, uint false_branch) : base(nodes)
        {
            this.cond = cond;
            this.true_branch = null;
            this.false_branch = null;
            resolving_true_branch = true_branch;
            resolving_false_branch = false_branch;
            is_loop = false;
            is_do_loop = false;
            generated = false;
        }

        public bool IsIf()
        {
            return !is_loop && !is_switch;
        }

        public override void ResolveFlow(BasicBlock block)
        {
            uint target = block.idx;
            if (target == resolving_true_branch)
            {
                true_branch = block;
            }
            if (target == resolving_false_branch)
            {
                false_branch = block;
            }
            base.ResolveFlow(block);
        }

        public override void UpdateFlow(BasicBlock block)
        {
            if (!is_loop && !is_switch)
            {
                if (true_branch != null && true_branch.idx == block.idx)
                {
                    true_branch = block;
                }
                if (false_branch != null && false_branch.idx == block.idx)
                {
                    false_branch = block;
                }
            }
            if (is_loop)
            {
                if (continue_block != null && continue_block.idx == block.idx)
                {
                    continue_block = block;
                }
                if (loop_body != null && loop_body.idx == block.idx)
                {
                    loop_body = block;
                }

            }

            if (is_switch && cases_body != null)
            {
                for (int i = 0; i < cases_body.Length; i++)
                {
                    if (cases_body[i] != null && cases_body[i].idx == block.idx)
                    {
                        cases_body[i] = block;
                    }
                }
            }
            base.UpdateFlow(block);
        }

        public override void ForEachNext(Func<BasicBlock, bool> callback)
        {
            if (IsIf())
            {
                if (true_branch != null)
                {
                    callback(true_branch);
                }
                if (false_branch != null)
                {
                    callback(false_branch);
                }
            }
            // we will not go to next for if block
            // base.ForEachNext(callback);
        }

        public void ForEachNextAll(Func<BasicBlock, bool> callback)
        {
            if (IsIf())
            {
                if (true_branch != null)
                {
                    callback(true_branch);
                }
                if (false_branch != null)
                {
                    callback(false_branch);
                }
            } else
            {
                if (is_loop)
                {
                    if (loop_body != null)
                    {
                        callback(loop_body);
                    }
                } else
                {
                    if (is_switch)
                    {
                        foreach (var bb in cases_body)
                        {
                            if (bb != null)
                            {
                                callback(bb);
                            }
                        }
                    }
                }
            }
        }
        public override bool IsNodeDiverge()
        {
            return true_branch != null && false_branch != null;
        }

        public override void GenerateCode(StringBuilder output, BasicBlock terminate, BasicBlock continueb, BasicBlock breakb, BasicBlock parent_next, int ident)
        {
            generated = true;
            var ident_str = new string('\t', ident);
            if (is_loop)
            {
                if (!is_do_loop)
                {
                    var cond_str = GenerateNodeCode(ident_str) + cond.ToString();
                    var cont_strsb = new StringBuilder();
                    if (continue_block != null)
                        continue_block.GenerateCode(cont_strsb, next, continueb, breakb, parent_next, ident + 1);
                    var loop_str = $"{ident_str}for (;\n{cond_str}; \n{cont_strsb}{ident_str}) {{";
                    output.Append(loop_str + "\n");
                    // output.Append($"{ident_str} // Loop Body = {loop_body.idx}; Continue = {continue_block.idx}; Next = {next.idx}" + "\n");
                    if (loop_body != terminate)
                    {
                        // loop has no parent next so all break/continue must be emit
                        loop_body.GenerateCode(output, next, continue_block, next, continue_block /* should be fine? */, ident + 1);
                    }
                    output.Append($"{ident_str}}}\n");
                } else
                {
                    var ident_str_1 = new string('\t', ident + 1);
                    output.Append($"{ident_str}do {{\n");
                    output.Append(GenerateNodeCode(ident_str_1) + "\n");
                    loop_body.GenerateCode(output, next, this, next, this /* maybe put this here? */, ident + 1);
                    output.Append($"{ident_str}}} while (true);\n");
                }
            } else
            {
                output.Append(GenerateNodeCode(ident_str) + "\n");
                if (is_switch)
                {
                    GenerateSwitchLike(output, cases_body, expressions.Select(x => x.ToString()).ToArray(), continueb, $"switch_{switch_type.ToString().ToLower()}", value.ToString(), ident);
                } 
                else
                {
                    //var if_str = $"{ident_str}if ({cond}) {{";
                    //output.AppendLine(if_str);
                    var tsb = new StringBuilder();
                    var fsb = new StringBuilder();
                    if (true_branch != null)
                    {
                        GenerateNextCode(true_branch, tsb, next, ident + 1, continueb, breakb, next, ident_str + "\t");
                    }
                    // output.AppendLine($"{ident_str}}}");
                    if (false_branch != null)
                    {
                        //var else_str = $"{ident_str}else\n{ident_str}{{";
                        //output.AppendLine(else_str);
                        GenerateNextCode(false_branch, fsb, next, ident + 1, continueb, breakb, next, ident_str + "\t");
                        //output.AppendLine($"{ident_str}}}");
                    }
                    var true_str = tsb.ToString();
                    var false_str = fsb.ToString();
                    if (true_str.Trim() != "" && false_str.Trim() != "")
                    {
                        output.Append($"{ident_str}if ({cond}) {{" + "\n");
                        output.Append(true_str);
                        output.Append($"{ident_str}}} else {{" + "\n");
                        output.Append(false_str);
                        output.Append($"{ident_str}}}\n");
                    }
                    else
                    {
                        if (true_str.Trim() != "")
                        {
                            output.Append($"{ident_str}if ({cond}) {{" + "\n");
                            output.Append(true_str);
                            output.Append($"{ident_str}}}" + "\n");
                        }
                        else
                        {
                            if (false_str.Trim() != "")
                            {
                                output.Append($"{ident_str}if (!({cond})) {{" + "\n");
                                output.Append(false_str);
                                output.Append($"{ident_str}}}" + "\n");
                            }
                        }
                    }
                }
                
            }
            GenerateNextCode(next, output, terminate, ident, continueb, breakb, parent_next, ident_str);
        }
    }

    public class GoToBasicBlock : BasicBlock
    {
        public bool is_continue;
        public GoToBasicBlock(ASTNode[] nodes, uint next_block) : base(nodes)
        {
            resolving_next = next_block;
        }

        public override void GenerateCode(StringBuilder output, BasicBlock terminate, BasicBlock continueb, BasicBlock breakb, BasicBlock parent_next, int ident)
        {
            generated = true;
            var ident_str = new string('\t', ident);
            if (nodes != null && nodes.Length > 0)
                output.Append(GenerateNodeCode(ident_str) + "\n");
            if (!next.generated)
            {
                GenerateNextCode(next, output, terminate, ident, continueb, breakb, parent_next, ident_str);
            } else
            {
                // TODO: need to avoid generate the code too early?
                // say put the return at the beginning..
                if (!is_continue)
                    if (next != terminate)
                        GenerateNextCode(next, output, terminate, ident, continueb, breakb, parent_next, ident_str);
                //output.Append($"{ident_str}goto .L{next.idx};" + "\n");
            }
        }
    }

    public class ComputeGoToBlock : BasicBlock
    {
        uint[] resolving_nexts;
        BasicBlock[] nexts;
        ASTNode cond;
        public ComputeGoToBlock(ASTNode[] nodes, ASTNode cond, uint[] resolving_nexts) : base(nodes)
        {
            this.cond = cond;
            this.resolving_nexts = resolving_nexts;
            nexts = new BasicBlock[resolving_nexts.Length];
        }

        public override void ResolveFlow(BasicBlock block)
        {
            uint target = block.idx;
            for (int i = 0; i < resolving_nexts.Length; i++)
            {
                if (target == resolving_nexts[i])
                {
                    nexts[i] = block;
                }
            }
            base.ResolveFlow(block);
        }

        public override void ForEachNext(Func<BasicBlock, bool> callback)
        {
            foreach (var bb in nexts)
            {
                if (bb != null)
                {
                    callback(bb);
                }
            }
            // base.ForEachNext(callback);
        }

        public override void UpdateFlow(BasicBlock block)
        {
            for (int i = 0; i < nexts.Length; i++)
            {
                if (nexts[i] != null && nexts[i].idx == block.idx)
                {
                    nexts[i] = block;
                }
            }
            base.UpdateFlow(block);
        }

        public override bool IsNodeDiverge()
        {
            return nexts.Length > 1;
        }

        public override void GenerateCode(StringBuilder output, BasicBlock terminate, BasicBlock continueb, BasicBlock breakb, BasicBlock parent_next, int ident)
        {            
            generated = true;
            var ident_str = new string('\t', ident);
            var ident_str_1 = new string('\t', ident + 1);
            var ident_str_2 = new string('\t', ident + 2);
            output.Append(GenerateNodeCode(ident_str) + "\n");
            /*
            var cond_str = cond.ToString();
            output.Append($"{ident_str}switch_compute ({cond_str}) {{\n");
            var merged = new Dictionary<BasicBlock, List<uint>>();

            for (int i = 0; i < nexts.Length; i++)
            {
                if (nexts[i] != null)
                {
                    var real_next = nexts[i];
                    if (nexts[i] is GoToBasicBlock gbb && gbb.nodes.Length == 0 && gbb.next != null)
                    {
                        real_next = nexts[i].next;
                    }
                    if (! merged.ContainsKey(real_next))
                    {
                        merged[real_next] = new List<uint>();
                    }
                    merged[real_next].Add(nexts[i].line_start);
                }
            }
            foreach (var kv in merged)
            {
                output.Append(string.Join("\n", kv.Value.Select((x) => $"{ident_str_1}case {x}:")) + "{\n");
                GenerateNextCode(kv.Key, output, next, ident + 2, continueb, next, null, ident_str_2);
                output.Append($"{ident_str_1}}}\n");
            }*/
            GenerateSwitchLike(output, nexts, null, continueb, "switch_compute", cond.ToString(), ident);
            /*
            for (int i = 0; i < nexts.Length; i++)
            {
                if (nexts[i] != null)
                {
                    output.Append($"{ident_str_1}case {nexts[i].line_start}: {{\n");
                    GenerateNextCode(nexts[i], output, next, ident + 2, continueb, next, ident_str_2);
                    //nexts[i].GenerateCode(output, next, ident + 1);
                    output.Append($"{ident_str_1}}}\n");
                }
            }*/
            output.Append($"{ident_str}}}\n");
            GenerateNextCode(next, output, terminate, ident, continueb, breakb, parent_next, ident_str);
        }
    }

    public class ReturnBasicBlock : BasicBlock
    {
        public ReturnBasicBlock(ASTNode[] nodes) : base(nodes)
        {
        }
    }
    
    UAsset Asset;
    TextWriter Output;
    Dictionary<string, string> importkey_to_name;
    Dictionary<string, bool> name_imported;

    struct ImportOne
    {
        public string shortpath;
        public string alias;
        public override string ToString()
        {
            if (shortpath == alias)
            {
                return alias;
            }
            else
            {
                return $"{shortpath} as {alias}";
            }
        }
    }
    struct ImportInfo
    {
        public string longpath;
        public List<ImportOne> importones;
        public ImportInfo(string longpath)
        {
            this.longpath = longpath;
            this.importones = new List<ImportOne>();
        }
        public override string ToString()
        {
            if (importones.Count == 0)
            {
                return $"from {longpath} import *;";
            } else
            {
                if (importones.Count == 1)
                {
                    return $"from {longpath} import {importones[0]}";
                } else
                {
                    return $"from {longpath} import {{{string.Join(", ", importones.Select(x => x.ToString()))}}};";
                }
            }
        }
    }

    Dictionary<string, ImportInfo> import_table;
    enum ReferenceType
    {
        LP = 0x1,
        L = 0x10,
        C = 0x100
    }
    Dictionary<uint, ReferenceType> referencedAddresses = new Dictionary<uint, ReferenceType>();
    string GetRefString(uint line, ReferenceType t)
    {
        List<string> ls = new List<string>();
        foreach (ReferenceType e in Enum.GetValues(typeof(ReferenceType)))
        {
            if ((t & (ReferenceType) e) == (ReferenceType) e)
            {
                ls.Add($".{e.ToString()}{line}:");
            }
        }
        return string.Join("\n", ls);
    }
    public Decompiler(UAsset asset, TextWriter output) {
        Asset = asset;
        Output = output;
        importkey_to_name = new Dictionary<string, string>();
        name_imported = new Dictionary<string, bool>();
        import_table = new Dictionary<string, ImportInfo>();
        referencedAddresses = new Dictionary<uint, ReferenceType>();
    }

    public string FindUniqueName(string name)
    {
        if (name_imported.ContainsKey(name))
        {
            int i = 1;
            while (name_imported.ContainsKey(name + "_" + i.ToString()))
            {
                i++;
            }
            name_imported[name + "_" + i.ToString()] = true;
            return name + "_" + i.ToString();
        }
        else
        {
            name_imported[name] = true;
            return name;
        }
    }

    public void EmplaceTable(string longpath, string shortpath, string alias)
    {
        if (!import_table.ContainsKey(longpath))
        {
            import_table[longpath] = new ImportInfo(longpath);
        }
        import_table[longpath].importones.Add(new ImportOne { shortpath = shortpath, alias = alias });
    }
    public string CheckImport(FPackageIndex index)
    {
        if (index.IsImport())
        {
            var shortname = ToString(index);
            var longstr = ToStringImport(index);
            var import_key = $"{shortname}::{longstr}";
            if (importkey_to_name.ContainsKey(import_key))
            {
                return importkey_to_name[import_key];
            }
            else
            {
                var unique_name = FindUniqueName(shortname);
                importkey_to_name[import_key] = unique_name;
                EmplaceTable(longstr, shortname, unique_name);
                /*
                if (unique_name != shortname)
                {
                    import_table.Add(longstr, new ImportOne { shortpath = shortname, alias = unique_name });
                    import_table.Add($"import {import_key} as {unique_name}");
                } else
                {

                    import_table.Add($"from {longstr} import {shortname}");
                }*/
                return unique_name;
            }
        } 
        else
        {
            return ToString(index);
        }
    }

    public string normalizeProperty(string name)
    {
        var match = Regex.Match(name, @"(.*)Property");
        if (match.Success)
        {
            return match.Groups[1].Value;
        }
        return name;
    }
    public string PropPreciseType(FProperty prop)
    {
        switch (prop)
        {
            case FArrayProperty p:
                return $"Array<{PropPreciseType(p.Inner)}>";
            case FMapProperty p:
                return $"Map<{PropPreciseType(p.KeyProp)}, {PropPreciseType(p.ValueProp)}>";
            case FSetProperty p:
                return $"Set<{PropPreciseType(p.ElementProp)}>";
            case FStructProperty p:
                return CheckImport(p.Struct);
            case FInterfaceProperty p:
                return $"Interface<{CheckImport(p.InterfaceClass)}>";
            case FSoftObjectProperty p:
                return $"SoftObject<{CheckImport(p.PropertyClass)}>";
            case FSoftClassProperty p:
                return $"SoftClass<{CheckImport(p.PropertyClass)}>";
            case FDelegateProperty p:
                return $"Delegate<{CheckImport(p.SignatureFunction)}>";
            case FEnumProperty p:
                return $"{CheckImport(p.Enum)} as {PropPreciseType(p.UnderlyingProp)}";
            case FByteProperty _:
                return "byte";
            case FBoolProperty _:
                return "bool";
            case FNumericProperty _:
                return "Numeric";
            case FObjectProperty p:
                return CheckImport(p.PropertyClass);
            case FGenericProperty p:
                switch (p.SerializedType.ToString())
                {
                    case "StrProperty":
                        return "string";
                    case "NameProperty":
                        return "Name";
                    case "TextProperty":
                        return "Text";
                    default:
                        return normalizeProperty(p.SerializedType.ToString());
                }
            default:
                return normalizeProperty(prop.SerializedType.ToString());
        }
    }

    bool StragedyResolveIfNot(ASTNode[] nodes, Dictionary<uint, ReferenceType> refmap)
    {
        for (int i = 0; i < nodes.Length; i++)
        {
            if (nodes[i] is IfNotNode ifnot)
            {
                var true_branch = nodes[i + 1].line;
                MarkAddress(true_branch, ReferenceType.L, refmap);
                nodes[i] = ifnot.ToIfNode((int) true_branch);
            }

            if (nodes[i] is EndOfThreadIfNotNode endofthreadifnot)
            {
                var true_branch = nodes[i + 1].line;
                MarkAddress(true_branch, ReferenceType.L, refmap);
                nodes[i] = endofthreadifnot.ToIfNode((int) true_branch);
            }
        }
        return true;
    }

    enum BranchHistory
    {
        Never,
        TakenTrue,
        TakenFalse,
    }


    bool ResolvePushPopScan(int idx, int computed_jump, ASTNode[] nodes, Stack<uint> stack, Dictionary<int, BranchHistory> branchHistory, Dictionary<int, int> resolvedPop, Dictionary<int, bool> visited)
    {
        int i = idx;
        while (i < nodes.Length)
        {
            visited[i] = true;
            switch (nodes[i])
            {
                case PushFlowNode push:
                    stack.Push(push.target);
                    if (!ResolvePushPopScan(i + 1, computed_jump, nodes, stack, branchHistory, resolvedPop, visited))
                    {
                        return false;
                    } else
                    {
                        stack.Pop();
                    }
                    return true;
                case IfNode ifnode:
                    if (branchHistory[i] == BranchHistory.Never)
                    {
                        branchHistory[i] = BranchHistory.TakenTrue;
                        if (!ResolvePushPopScan(ifnode.true_branch, computed_jump, nodes, stack, branchHistory, resolvedPop, visited))
                        {
                            return false;
                        }
                        branchHistory[i] = BranchHistory.TakenFalse;
                        if (!ResolvePushPopScan(ifnode.false_branch, computed_jump, nodes, stack, branchHistory, resolvedPop, visited))
                        {
                            return false;
                        }
                        branchHistory[i] = BranchHistory.Never;
                        return true;
                    }
                    else
                    {
                        return true;
                    }
                case GotoNode gotoNode:
                    i = gotoNode.jump;
                    continue;
                case EndOfThreadNode:
                    Console.WriteLine($"Pop at {i} in function ${gFunctionName}");
                    if (branchHistory[i] == BranchHistory.Never)
                    {
                        if (stack.Count > 0)
                        {
                            var target = (int) stack.Pop();
                            if (resolvedPop.ContainsKey(i))
                            {
                                if (resolvedPop[i] != target)
                                {
                                    Console.WriteLine($"Multiple resolved pops at {i} {resolvedPop[i]} {target} in function ${gFunctionName}");
                                    return false;
                                }
                            }
                            Console.WriteLine($"Pop at {i} resolved target = {target}");
                            resolvedPop[i] = target;
                            branchHistory[i] = BranchHistory.TakenTrue;
                            if (!ResolvePushPopScan(target, computed_jump, nodes, stack, branchHistory, resolvedPop, visited))
                            {
                                return false;
                            }
                            stack.Push((uint) target);
                            branchHistory[i] = BranchHistory.Never;
                            return true;
                        }
                        else
                        {
                            throw new Exception("Stack underflow");
                        }
                    } else
                    {

                        if (stack.Count > 0)
                        {
                            var target = (int) stack.Pop();
                            if (resolvedPop.ContainsKey(i))
                            {
                                if (resolvedPop[i] != target)
                                {
                                    Console.WriteLine($"Multiple resolved pops at {i} {resolvedPop[i]} {target} in function ${gFunctionName}");
                                    return false;
                                }
                            }
                            stack.Push((uint) target);
                            resolvedPop[i] = target;
                        }
                        else
                        {
                            throw new Exception("Stack underflow");
                            
                        }
                    }
                    return true;
                case EndOfThreadIfNode nd:
                    Console.WriteLine($"Pop at {i} in function ${gFunctionName}");
                    if (branchHistory[i] == BranchHistory.Never)
                    {
                        branchHistory[i] = BranchHistory.TakenTrue;
                        if (!ResolvePushPopScan(nd.true_branch, computed_jump, nodes, stack, branchHistory, resolvedPop, visited))
                        {
                            return false;
                        }
                        if (stack.Count > 0)
                        {
                            var target = (int)stack.Pop();
                            if (resolvedPop.ContainsKey(i))
                            {
                                if (resolvedPop[i] != target)
                                {
                                    Console.WriteLine($"Multiple resolved pops at {i} {resolvedPop[i]} {target} in function ${gFunctionName}");
                                    return false;
                                }
                            }
                            Console.WriteLine($"Pop at {i} resolved target = {target}");
                            resolvedPop[i] = target;
                            branchHistory[i] = BranchHistory.TakenFalse;
                            if (!ResolvePushPopScan(target, computed_jump, nodes, stack, branchHistory, resolvedPop, visited))
                            {
                                return false;
                            }
                            stack.Push((uint) target);
                            branchHistory[i] = BranchHistory.Never;
                            return true;
                        }
                        else
                        {
                            throw new Exception("Stack underflow");
                        }
                    } else {
                        if (stack.Count > 0)
                        {
                            var target = (int)stack.Pop();
                            if (resolvedPop.ContainsKey(i))
                            {
                                if (resolvedPop[i] != target)
                                {
                                    Console.WriteLine($"Multiple resolved pops at {i} {resolvedPop[i]} {target} in function ${gFunctionName}");
                                    return false;
                                }
                            }
                            stack.Push((uint) target);
                        }
                        else
                        {
                            throw new Exception("Stack underflow");
                        }
                    }
                    return true;
                case GotoComputeNode gcn:
                    if (computed_jump <= i)
                    {
                        gcn.resolved_jumps.Add((uint) i + 1);
                        i = i + 1;
                    } else
                    {
                        gcn.resolved_jumps.Add((uint) computed_jump);
                        i = computed_jump;
                    }
                    continue;
            }
            i++;
        }
        return true;
    }

    Dictionary<uint, ReferenceType> StragedyLineToIdx(ASTNode[] nodes, Dictionary<uint, ReferenceType> refmap)
    {
        Dictionary<uint, uint> lineidx = new Dictionary<uint, uint>();
        for (uint i = 0; i < nodes.Length; i++)
        {
            lineidx[nodes[i].line] = i;
        }

        // check if all references exist
        var addressRename = new Dictionary<uint, uint>();
        foreach (var pair in refmap)
        {
            if (!lineidx.ContainsKey(pair.Key))
            {
                uint nearest = 0x7fffffff;
                foreach (var line in lineidx.Keys)
                {
                    if (line > pair.Key && line < nearest)
                    {
                        nearest = line;
                    }
                }
                addressRename[pair.Key] = nearest;
            }
        }
        // update referencedAddresses
        foreach (var pair in addressRename)
        {
            if (refmap.ContainsKey(pair.Key))
            {
                // change key
                MarkAddress(pair.Value, refmap[pair.Key], refmap);
                // remove pair.key
                refmap.Remove(pair.Key);
            }
        }

        // update all nodes
        for (int i = 0; i < nodes.Length; i++)
        {
            nodes[i].RenameIdx(addressRename);
            nodes[i].RenameIdx(lineidx);
        }

        Dictionary<uint, ReferenceType> newrefmap = new Dictionary<uint, ReferenceType>();

        foreach (var pair in refmap)
        {
            newrefmap[lineidx[pair.Key]] = pair.Value;
        }

        return newrefmap;
    }

    bool StragedyResolvePushPop(ASTNode[] nodes, Dictionary<uint, ReferenceType> refmap)
    {
        Stack<uint> stack = new Stack<uint>();
        Dictionary<int, BranchHistory> branchHistory = new Dictionary<int, BranchHistory>();
        Dictionary<int, int> resolvedPop = new Dictionary<int, int>();
        bool needResolve = false;
        
        for (int i = 0; i < nodes.Length; i++)
        {
            if (nodes[i] is IfNode || nodes[i] is EndOfThreadIfNode || nodes[i] is EndOfThreadNode)
            {
                branchHistory[i] = BranchHistory.Never;
                if (nodes[i] is EndOfThreadIfNode || nodes[i] is EndOfThreadNode)
                {
                    needResolve = true;
                }
            }
        }
        Dictionary<int, bool> visited = new Dictionary<int, bool>();
        for (int i = 0; i < nodes.Length; i++)
        {
            visited[i] = false;
        }
        
        for (int i = 0; i < nodes.Length; i++)
        {
            if (!visited[i])
            {
                if (i != 0)
                {
                    if (gFunctionName == debugging_function) { 
                    
                    Console.WriteLine($"Unreachable code at {i} in function ${gFunctionName}, try resolve");
                    }
                }
                if (!ResolvePushPopScan(0, i, nodes, stack, branchHistory, resolvedPop, visited))
                {
                    return false;
                }
            }
        }
        // all resolved?
        for (int i = 0; i < nodes.Length; i++)
        {
            switch (nodes[i])
            {
                case EndOfThreadNode eot:
                    if (!resolvedPop.ContainsKey(i))
                    {
                        Console.WriteLine($"Unresolved EndOfThread at {i} in function ${gFunctionName}");
                        return false;
                    }
                    else
                    {
                        nodes[i] = new GotoNode(eot.line, resolvedPop[i]);
                        nodes[i].idx = (uint)i;
                    }
                    break;
                case EndOfThreadIfNode eot:
                    if (!resolvedPop.ContainsKey(i))
                    {
                        Console.WriteLine($"Unresolved EndOfThreadIf at {i} in function ${gFunctionName}");
                        return false;
                    }
                    else
                    {
                        nodes[i] = new IfNode(eot.line, eot.cond, eot.true_branch, resolvedPop[i]);
                        nodes[i].idx = (uint)i;
                    }
                    break;
                case PushFlowNode:
                    nodes[i].nop();
                    break;
                case GotoComputeNode gpn:
                    foreach (var target in gpn.resolved_jumps)
                    {
                        MarkAddress(target, ReferenceType.L, refmap);
                    }
                    break;
            }
        }
        if (needResolve)
        {
            Console.WriteLine($"Success resolved pushpop in function {gFunctionName}");
        }
        return true;
    }

    ASTNode[] GetNodes(ASTNode[] src, uint start_idx, uint end_idx)
    {
        ASTNode[] result = new ASTNode[end_idx - start_idx];
        for (uint i = start_idx; i < end_idx; i++)
        {
            result[i - start_idx] = src[i];
        }
        return result;
    }

    static void SubscribeResolver(int idx, BasicBlock bb, Dictionary<uint, List<BasicBlock>> bb_resolver)
    {
        if (!bb_resolver.ContainsKey((uint)idx))
        {
            bb_resolver[(uint)idx] = new List<BasicBlock> ();
        }
        bb_resolver[(uint)idx].Add(bb);
    }
    BasicBlock? StragedyRecursiveBBCreate(ASTNode[] nodes, Dictionary<uint, ReferenceType> refmap)
    {
        Dictionary<uint, BasicBlock> bb_table = new Dictionary<uint, BasicBlock>();
        Dictionary<uint, List<BasicBlock>> bb_resolver = new Dictionary<uint, List<BasicBlock>>();
        uint start_idx = 0;
        for (uint end_idx = 0; end_idx < nodes.Length; end_idx++)
        {
            // [start_idx...end_idx - 1] is a new block
            if (refmap.ContainsKey(end_idx))
            {
                if (end_idx - start_idx > 0)
                {
                    var new_nodes = GetNodes(nodes, start_idx, end_idx);
                    var block = new BasicBlock(new_nodes);
                    block.resolving_next = end_idx;
                    bb_table[start_idx] = block;
                    block.idx = start_idx;
                    block.line_start = nodes[start_idx].line;
                    block.line_end = nodes[end_idx - 1].line;
                    SubscribeResolver((int)nodes[end_idx].idx, block, bb_resolver);
                    start_idx = end_idx;
                }
            }

            // [start_idx...end_idx] is a new block
            switch (nodes[end_idx])
            {
                // control-flow related nodes
                case IfNode ifnode:
                    {
                        var new_nodes = GetNodes(nodes, start_idx, end_idx);
                        var block = new IfOrLoopOrSwitchBasicBlock(new_nodes, ifnode.cond, (uint)ifnode.true_branch, (uint)ifnode.false_branch);
                        bb_table[start_idx] = block;
                        block.idx = start_idx;
                        block.line_start = nodes[start_idx].line;
                        block.line_end = nodes[end_idx].line;
                        SubscribeResolver(ifnode.true_branch, block, bb_resolver);
                        SubscribeResolver(ifnode.false_branch, block, bb_resolver);
                        start_idx = end_idx + 1;
                        continue;
                    }
                case GotoNode gotonode:
                    {
                        var new_nodes = GetNodes(nodes, start_idx, end_idx);
                        var block = new GoToBasicBlock(new_nodes, (uint)gotonode.jump);
                        bb_table[start_idx] = block;
                        block.idx = start_idx;
                        block.line_start = nodes[start_idx].line;
                        block.line_end = nodes[end_idx].line;
                        SubscribeResolver(gotonode.jump, block, bb_resolver);
                        start_idx = end_idx + 1;
                        continue;
                    }
                case GotoComputeNode gotonode:
                    {
                        var new_nodes = GetNodes(nodes, start_idx, end_idx);
                        var block = new ComputeGoToBlock(new_nodes, gotonode.jump, gotonode.resolved_jumps.ToArray());
                        bb_table[start_idx] = block;
                        block.idx = start_idx;
                        block.line_start = nodes[start_idx].line;
                        block.line_end = nodes[end_idx].line;
                        foreach (var jline in gotonode.resolved_jumps)
                        {
                            SubscribeResolver((int) jline, block, bb_resolver);
                        }
                        start_idx = end_idx + 1;
                        continue;
                    }
                case ReturnNode ret:
                    {
                        // put the return into the block
                        var new_nodes = GetNodes(nodes, start_idx, end_idx + 1);
                        var block = new ReturnBasicBlock(new_nodes);
                        bb_table[start_idx] = block;
                        block.line_start = nodes[start_idx].line;
                        block.line_end = nodes[end_idx].line;
                        block.idx = start_idx;
                        SubscribeResolver((int) start_idx, block, bb_resolver);
                        start_idx = end_idx + 1;
                        continue;
                    }
            }
        }

        Dictionary<uint, bool> reachbility = new Dictionary<uint, bool>();
        foreach (var pk in bb_table)
        {
            reachbility[pk.Key] = false;
            if (bb_resolver.ContainsKey(pk.Key))
            {
                foreach (var bb in bb_resolver[pk.Key])
                {
                    bb.ResolveFlow(pk.Value);
                }
            }
        }

        // resolve next node for if?
        bool recursiveReach(BasicBlock bb)
        {
            if (reachbility[bb.idx])
                return true;
            reachbility[bb.idx] = true;
            bb.ForEachNext(recursiveReach);
            return true;
        };

        recursiveReach(bb_table[0]);

        bool okay = reachbility.All((x) => { return x.Value; });
        if (!okay)
        {
            Console.WriteLine($"Sanity check: Not all nodes are reachiable in {gFunctionName}: " + string.Join(", ", reachbility.Where((x) => x.Value == false).Select((x)=>x.Key).ToArray()));
            return null;
        }

        return bb_table[0];
    }

    static string debugging_function = "ExecuteUbergraph_WBP_IngameMenu_PalBox";
    bool updateBlock(BasicBlock bb, BasicBlock new_bb, Dictionary<uint, bool> visited)
    {
        if (visited.ContainsKey(bb.idx))
            return true;
        visited[bb.idx] = true;
        bb.UpdateFlow(new_bb);
        bb.ForEachNext((x) => updateBlock(x, new_bb, visited));
        return true;
    }

    bool StragedyCreateNextForLoopAndIf(BasicBlock bb_root)
    {
        // if a if node, search for it first, then use the found next for previous if to skip the middle
        Stack<BasicBlock> fullpath = new Stack<BasicBlock>();
        Stack<IfOrLoopOrSwitchBasicBlock> ifpath = new Stack<IfOrLoopOrSwitchBasicBlock>();

        BasicBlock? resolveFarestBlock(BasicBlock bb)
        {
            try
            {
                fullpath.Push(bb);
                if (bb.next == null)
                {
                    return bb;
                }
                BasicBlock? result = null;
                bb.QuickNext((x) =>
                {
                    if (!fullpath.Contains(x))
                    {
                        result = resolveFarestBlock(x);
                    }
                    return true;
                });
                return result;
            } finally
            {
                fullpath.Pop();
            }
        }

        // this function should never enter a loop twice
        bool resolveNextForIf(BasicBlock bb, BasicBlock? ifnode, Dictionary<uint, bool> colormap, int depth = 0)
        {
            try
            {
                fullpath.Push(bb);
                string pads = new String('\t', depth + 1);
                if (gFunctionName == debugging_function)
                {
                    Console.WriteLine($"{pads}Visit Node {bb.idx}");
                }
                if (colormap.ContainsKey(bb.idx))
                {
                    if (ifnode != null)
                    {
                        ifnode.next = bb;
                    }
                    return true;
                }
                colormap[bb.idx] = true;
                if (bb is ComputeGoToBlock goton)
                {
                    bool okay = true;
                    bb.ForEachNext((x) =>
                    {
                        okay &= resolveNextForIf(x, bb, colormap, depth + 1);
                        return true;
                    });
                    List<BasicBlock?> resultBlocks = new List<BasicBlock>();
                    bb.ForEachNext((x) => {
                        resultBlocks.Add(resolveFarestBlock(x));
                        return true;
                    });
                    if (resultBlocks.Any() && resultBlocks.All(x => x == resultBlocks.First()))
                    {
                        bb.next = resultBlocks.First();
                    }
                    return okay;
                } else
                if (bb is IfOrLoopOrSwitchBasicBlock ifbb)
                {
                    if (ifbb.IsIf())
                    {
                        try
                        {
                            ifpath.Push(ifbb);
                            if (gFunctionName == debugging_function)
                            {
                                if (ifbb.true_branch != null  && ifbb.false_branch != null)
                                    Console.WriteLine($"{pads} is if block, next = {ifbb.true_branch.idx}, {ifbb.false_branch.idx}");
                                else
                                {
                                    if (ifbb.true_branch != null)
                                        Console.WriteLine($"{pads} is if block, next = {ifbb.true_branch.idx}");
                                    if (ifbb.false_branch != null)
                                        Console.WriteLine($"{pads} is if block, next = {ifbb.false_branch.idx}");
                                }
                            }

                            if (bb.next != null)
                            {
                                if (!resolveNextForIf(bb.next, ifnode, colormap, depth))
                                    return false;
                                return true;
                            }

                            bool okay = true;
                            var nextColor = new Dictionary<uint, bool>();
                            bb.ForEachNext((x) =>
                            {
                                okay &= resolveNextForIf(x, bb, nextColor, depth + 1);
                                return true;
                            });
                            if (ifbb.next == null)
                            {
                                Console.WriteLine($"{(gFunctionName == debugging_function ? pads : "")}Failed to resolve next for if @{bb.idx} in function {gFunctionName}");
                                return false;
                            }
                            else
                            {
                                if (gFunctionName == debugging_function)
                                {
                                    Console.WriteLine($"{pads}Resolved bb@{bb.idx} == {bb.next.idx}");
                                }
                            }
                            if (!resolveNextForIf(ifbb.next, ifnode, colormap, depth + 1))
                                return false;
                            return okay;
                        }
                        finally
                        {
                            ifpath.Pop();
                        }
                    } else
                    {
                        // this is not an if, so it must be resolved, we only care about next
                        if (!resolveNextForIf(ifbb.next, ifnode, colormap, depth + 1))
                            return false;
                        return true;
                    }
                }
                else
                {
                    bool okay = true;
                    bb.ForEachNext((x) =>
                    {
                        // end analysis at loop back
                        if (! fullpath.Contains(x))
                        {
                            okay &= resolveNextForIf(x, ifnode, colormap, depth + 1);
                        }
                        else
                        {
                            void forloophandle(IfOrLoopOrSwitchBasicBlock if_prev, GoToBasicBlock gbb)
                            {
                                if_prev.next = if_prev.false_branch;
                                if_prev.continue_block = bb;
                                if_prev.loop_body = if_prev.true_branch;
                                if_prev.is_loop = true;
                                gbb.is_continue = true;
                                if (gFunctionName == debugging_function)
                                {
                                    Console.WriteLine($"{pads}Resolved loop@{if_prev.idx}, next = {if_prev.next.idx}, continue = {bb.idx}");
                                }
                                okay &= resolveNextForIf(if_prev.next, ifnode, colormap, depth + 1);
                            }

                            IfOrLoopOrSwitchBasicBlock doloophandle(IfOrLoopOrSwitchBasicBlock if_prev, GoToBasicBlock gbb)
                            {
                                var new_loop = new IfOrLoopOrSwitchBasicBlock(new ASTNode[0], null, 0x7fffffff, 0x7fffffff);
                                new_loop.is_do_loop = true;
                                new_loop.is_loop = true;
                                new_loop.line_start = x.line_start;
                                new_loop.line_end = x.line_end;
                                new_loop.next = if_prev.false_branch; // out of loop
                                new_loop.continue_block = null;
                                new_loop.idx = x.idx;
                                if_prev.next = gbb;
                                // prev.next = prev.true_branch.next;
                                gbb.is_continue = true;
                                // we cannot simply replace, because x maybe a if or control-flow block
                                updateBlock(bb_root, new_loop, new Dictionary<uint, bool>());
                                new_loop.loop_body = x; // <-- this maybe continue block, but we can't mark it on this garmmar
                                x.idx |= (1 << 24);
                                return new_loop;
                            }
                            // found a loop back on path
                            if (ifpath.Contains(x))
                            {
                                var if_prev = (IfOrLoopOrSwitchBasicBlock)x;
                                if (if_prev.is_loop)
                                {
                                    if (if_prev.continue_block != bb)
                                    {
                                        Console.WriteLine($"Unmerged Loop detected, node {if_prev.idx} has two continue blocks ${bb.idx} and {if_prev.continue_block.idx}");
                                    }
                                }
                                else
                                {
                                    if (bb is GoToBasicBlock gbb)
                                    {

                                        if (bb.next.nodes[0] is PushFlowNode)
                                        {
                                            // case 2, the loop cond is at the end of the loop
                                            /*
                                             * begin:
                                             * push(continue)
                                             * **<add a loop node here>**
                                             * loop_body (may contain if and being recognized as the frist case, but it's actually do-loop)
                                             *  ALSO, THIS MAYBE A BREAK in do-loop
                                             * pop(continue)
                                             * i++
                                             * if (!loop) goto end
                                             * goto begin
                                             * end:
                                             */
                                            if (ifpath.Count >= 1)
                                            {
                                                // maybe do-loop
                                                var prev = ifpath.Peek();
                                                if (prev.IsIf())
                                                {
                                                    // soudns like a do-loop
                                                    var new_loop = doloophandle(prev, gbb);
                                                    // WARN: x is invalid from now
                                                    okay &= resolveNextForIf(new_loop.next, ifnode, colormap, depth + 1);
                                                }
                                            }
                                        }
                                        else
                                        {

                                            // case 1, the loop cond is at the beginning of the loop
                                            /*
                                             * begin:
                                             * if (! loop) goto end (need ensure this if jump out of the loop)
                                             * loop_var = next_var
                                             * push(continue)
                                             * loop_body
                                             * pop(continue)
                                             * continue:
                                             * i++
                                             * goto begin
                                             * end:
                                             */
                                            forloophandle(if_prev, gbb);
                                        }


                                    }
                                    else { 
                                        Console.WriteLine($"Unsupported Loop Pattern at function {gFunctionName} node {bb.idx}");
                                    }
                                }
                            }
                            else
                            {
                                if (ifpath.Count >= 1)
                                {
                                    // maybe do-loop
                                    if (bb is GoToBasicBlock gbb)
                                    {
                                        var prev = ifpath.Peek();
                                        if (prev.IsIf())
                                        {
                                            // soudns like a do-loop
                                            var new_loop = doloophandle(prev, gbb);
                                            // WARN: x is invalid from now
                                            okay &= resolveNextForIf(new_loop.next, ifnode, colormap, depth + 1);
                                        }
                                    }
                                } else
                                {
                                    okay &= resolveNextForIf(x, ifnode, colormap, depth + 1);
                                }
                            }
                        }
                        return true;
                    });
                    return okay;
                }
            } finally
            {
                fullpath.Pop();
            }
            
        }

        return resolveNextForIf(bb_root, null, new Dictionary<uint, bool>());

    }

    BasicBlock StragedyMergeSwitchBlocks(BasicBlock bb_root)
    {
        var k2switch = new Regex(@"K2Node_Switch(.*)_CmpSuccess");
        
        bool resolveNestedIf(BasicBlock bb, BasicBlock terminate, Stack<BasicBlock> path)
        {
            if (path.Contains(bb))
            {
                return true;
            }
            if (terminate == bb)
            {
                return true;
            }
            try
            {
                path.Push(bb);
                if (bb is IfOrLoopOrSwitchBasicBlock ifnode && ifnode.IsIf())
                {
                    var condstr = ifnode.cond.ToString().Trim();
                    var match = k2switch.Match(condstr);

                    if (match.Success)
                    {
                        Console.WriteLine($"Found Switch on {condstr} at {bb.idx} in function {gFunctionName}");
                        bool isLetAST(ASTNode x)
                        {
                            if (x is LetNode ln && ln.GetVariable().Trim() == condstr)
                            {
                                if (ln.expression is CallNode cn && cn.prefix == "$")
                                    return true;
                            }
                            return false;
                        }

                        // this should be the first if
                        if (!Enum.TryParse(match.Groups[1].ToString(), out SwitchType switch_type))
                        {
                            Console.WriteLine($"Unknown Switch Type on {condstr} at {bb.idx} in function {gFunctionName}");
                            return true;
                        }

                        var newnodes = ifnode.nodes.SkipLast(1).ToArray();

                        var new_switch_node = new IfOrLoopOrSwitchBasicBlock(newnodes, null, 0x7fffffff, 0x7fffffff);

                        new_switch_node.is_switch = true;
                        new_switch_node.switch_type = switch_type;
                        var letast = (LetNode)ifnode.nodes.Where(isLetAST).First();
                        var val = (ASTNode)((CallNode)letast.expression).args[0].Clone();
                        var valstr = val.ToString();
                        new_switch_node.value = val;
                        new_switch_node.next = bb.next;
                        new_switch_node.idx = bb.idx;
                        List<ASTNode> expressions = new List<ASTNode>();
                        List<BasicBlock> bbs = new List<BasicBlock>();
                        var cur = ifnode;
                        int idx = 0;
                        do
                        {
                            var body = cur.false_branch;
                            letast = (LetNode)cur.nodes.Where(isLetAST).First();
                            var valstr1 = ((CallNode)letast.expression).args[0].ToString();
                            if (valstr1 != valstr)
                            {
                                break;
                            }
                            var expression = (ASTNode)((CallNode)letast.expression).args[1].Clone();
                            expressions.Add(expression);
                            bbs.Add(body);

                            idx++;

                            if (cur.true_branch is IfOrLoopOrSwitchBasicBlock ifnext && ifnext.IsIf())
                            {
                                cur = ifnext;
                            } else
                            {
                                break;
                            }
                            if (cur.cond.ToString() != condstr)
                            {
                                break;
                            }
                        } while (true);

                        new_switch_node.expressions = new ASTNode[expressions.Count];
                        new_switch_node.cases_body = new BasicBlock[bbs.Count];
                        for (int i = 0; i < expressions.Count; i++)
                        {
                            new_switch_node.expressions[i] = expressions[i];
                            new_switch_node.cases_body[i] = bbs[i];
                        }

                        updateBlock(bb_root, new_switch_node, new Dictionary<uint, bool>());
                        if (bb_root.idx == new_switch_node.idx)
                        {
                            bb_root = new_switch_node;
                        }
                        path.Pop();
                        path.Push(new_switch_node);
                        new_switch_node.ForEachNextAll((x) => resolveNestedIf(x, new_switch_node.next, path));
                        resolveNestedIf(new_switch_node.next, terminate, path);
                    }
                } else
                {
                    if (bb is IfOrLoopOrSwitchBasicBlock ifnode1)
                    {
                        ifnode1.ForEachNextAll((x) => resolveNestedIf(x, ifnode1.next, path));
                        resolveNestedIf(ifnode1.next, terminate, path);
                    } else
                    {
                        resolveNestedIf(bb.next, terminate, path);
                    }
                }
            } finally
            {
                path.Pop();
            }
            return true;
        }
        resolveNestedIf(bb_root, null, new Stack<BasicBlock>());
        return bb_root;
    }
    Result CreateBasicBlock(ASTNode[] inputNodes)
    {
        var nodes = new ASTNode[inputNodes.Length];
        var refmap = new Dictionary<uint, ReferenceType>(referencedAddresses);
        for (int i = 0; i < inputNodes.Length; i++)
        {
            nodes[i] = (ASTNode)inputNodes[i].Clone();
        }

        // AST Node Phase
        if (!StragedyResolveIfNot(nodes, refmap))
        {
            return Err("Cannot Resolve all IfNot");
        }

        refmap = StragedyLineToIdx(nodes, refmap);

        if (refmap == null)
        {
            return Err("Cannot convert line to idx");
        }
        // TODO: create bb then reolve push/pop? so that we can duplicate node in this step
        if (!StragedyResolvePushPop(nodes, refmap))
        {
            return Err("Cannot Resolve Push & Pop");
        }
        var bb = StragedyRecursiveBBCreate(nodes, refmap);
        if (bb == null)
        {
            return Err("Cannot Create BB");
        }

        // Post BB Stragedy
        if (!StragedyCreateNextForLoopAndIf(bb))
        {
            return Err("Cannot resolve next for if (un-merged if)");
        }
        // TODO: merge switch block
        // if () if () if () if () ...
        bb = StragedyMergeSwitchBlocks(bb);
        if (bb == null)
        {
            return Err("Cannot merge switch blocks");
        }
        // TODO: reduce goto
        // Collect all (ifnode->next)->prev, count the one target that have largest hit,
        // check it this worth and if so make it the new next
        // fix the control flow by adding a goto node to those affected to its original prev
        // TODO: duplicate code path for gotos
        // if replace goto will not introduce too many code, replace it.
        return Ok(bb);
    }

    string PostGenerationRemoveUnusedLabel(string inputCode)
    {
        var lines = inputCode.Split("\n");
        StringBuilder stringBuilder = new StringBuilder();
        Dictionary<string, List<int>> labels = new Dictionary<string, List<int>>();
        Dictionary<string, bool> refs = new Dictionary<string, bool>();
        var reg_goto = new Regex(@"^\t*goto \.L(\d+);");
        var reg_label = new Regex(@"^\t*\.L(\d+):");
        for (int i = 0; i < lines.Length; i++)
        {
            var line = lines[i];
            var match_goto = reg_goto.Match(line);
            var match_label = reg_label.Match(line);
            if (match_goto.Success)
            {
                refs[match_goto.Groups[1].Value] = true;
            }
            if (match_label.Success) { 
            
                if (!labels.ContainsKey(match_label.Groups[1].Value))
                {
                    labels[match_label.Groups[1].Value] = new List<int>();
                }
                labels[match_label.Groups[1].Value].Add(i);
            }
        }
        foreach (var pk in labels)
        {
            if (!refs.ContainsKey(pk.Key))
            {
                foreach (var line in pk.Value)
                {
                    lines[line] = "";
                }
            }
        }
        for (int i = 0; i < lines.Length; i++)
        {
            if (lines[i] != "")
            {
                stringBuilder.Append(lines[i] + "\n");
            }
        }
        return stringBuilder.ToString();
    }

    //       
    static string removePrefix(string flagstr)
    {
        var match = Regex.Match(flagstr, @"^.*?_(.*)$");
        if (match.Success)
        {
            return match.Groups[1].Value;
        }
        return flagstr;
    }
    public bool Decompile() {
        StringBuilder stringBuilder = new StringBuilder();
        var anyExport = false;

        var classExport = Asset.GetClassExport();
        if (classExport != null) {
            anyExport = true;
            // EObjectFlags
            var cflags = new List<string>();
            bool isPublic = false;
            foreach (EObjectFlags flag in Enum.GetValues(typeof(EObjectFlags)))
            {
                if (flag != EObjectFlags.RF_NoFlags && classExport.ObjectFlags.HasFlag(flag))
                {
                    if (flag  == EObjectFlags.RF_Public)
                    {
                        isPublic = true;
                        continue;
                    }
                    cflags.Add(removePrefix(flag.ToString()));
                }
            }
            if (cflags.Count > 0)
            {
                stringBuilder.Append("@" + string.Join(" | ", cflags) + "\n");
            }
            var publicprefix = isPublic ? "pub " : "";
            stringBuilder.Append($"${publicprefix}class {classExport.ObjectName} {{" + "\n");
            foreach (var prop in classExport.LoadedProperties) {

                var flags = new List<string>();
                foreach (EPropertyFlags flag in Enum.GetValues(typeof(EPropertyFlags))) {
                    if (flag != EPropertyFlags.CPF_None && prop.PropertyFlags.HasFlag(flag)) {
                        flags.Add(removePrefix(flag.ToString()));
                    }
                }
                if (flags.Count > 0) {
                    stringBuilder.Append("\t@" + string.Join(" | ", flags) + "\n");
                }
                stringBuilder.Append($"\tvar {prop.Name}: {PropPreciseType(prop)};" + "\n");
            }
            stringBuilder.Append("\n");   
        } else {
            stringBuilder.Append("// no class export\n");
        }

        foreach (var export in Asset.Exports) {
            if (export is FunctionExport e) {
                var fflags = new List<string>();
                foreach (EFunctionFlags flag in Enum.GetValues(typeof(EFunctionFlags)))
                {
                    if (flag != EFunctionFlags.FUNC_None && flag != EFunctionFlags.FUNC_AllFlags && e.FunctionFlags.HasFlag(flag))
                    {
                        fflags.Add(removePrefix(flag.ToString()));
                    }
                }
                anyExport = true;

                string functionName = e.ObjectName.ToString();

                if (fflags.Count > 0)
                {
                    stringBuilder.Append($"\t@{string.Join(" | ", fflags)}" + "\n");
                }

                stringBuilder.Append($"\tfn {functionName}(");

                var fparams = new List<string>();
                var locals = new List<string>();
                var rettype = "void";
                foreach (var prop in e.LoadedProperties) {
                    var flags = new List<string>();
                    bool skip = false;
                    bool isParam = false;
                    bool isOutParam = false;
                    bool isConstParam = false;
                    bool isReadOnly = false;
                    foreach (EPropertyFlags flag in Enum.GetValues(typeof(EPropertyFlags))) {
                        if (flag != EPropertyFlags.CPF_None && prop.PropertyFlags.HasFlag(flag))
                        {
                            if (flag == EPropertyFlags.CPF_ReturnParm)
                            {
                                rettype = PropPreciseType(prop);
                                skip = true;
                                break;
                            }
                            if (flag == EPropertyFlags.CPF_Parm)
                            {
                                isParam = true;
                                continue;
                            }
                            if (flag == EPropertyFlags.CPF_OutParm)
                            {
                                isOutParam = true;
                                continue;
                            }
                            if (flag == EPropertyFlags.CPF_ConstParm)
                            {
                                isConstParam = true;
                                continue;
                            }
                            if (flag == EPropertyFlags.CPF_BlueprintReadOnly)
                            {
                                isReadOnly = true;
                                continue;
                            }
                            flags.Add(removePrefix(flag.ToString()));
                        }
                    }
                    if (skip) continue;
                    var ptype = PropPreciseType(prop);
                    var pname = prop.Name.ToString();

                    var flags_str = String.Join("|", flags);

                    if (isParam || isOutParam || isConstParam)
                    {
                        var pflags = new List<string>();
                        if (isConstParam) pflags.Add("const");
                        if (isOutParam) pflags.Add("out");
                        if (isReadOnly) pflags.Add("readonly");
                        var pflag = string.Join(" ", pflags);
                        if (flags.Count > 0)
                        {
                            fparams.Add($"{pname}: {pflag} {ptype} @{flags_str}");
                        } else
                        {
                            fparams.Add($"{pname}: {pflag} {ptype}");
                        }   
                    } else
                    {
                        // locals
                        if (flags.Count > 0)
                        {
                            locals.Add($"\t\tlocal {pname}: {ptype} @{flags_str};");
                        } else
                        {
                            locals.Add($"\t\tlocal {pname}: {ptype};");
                        }
                    }
                }
                var fparams_str = string.Join(", ", fparams);
                if (rettype != "void")
                {
                    stringBuilder.Append($"{fparams_str}) -> {rettype} {{" + "\n");
                } else
                {
                    stringBuilder.Append($"{fparams_str}) {{\n");
                }
                stringBuilder.Append(string.Join("\n", locals) + "\n");
                uint index = 0;
                ASTNode[] lines = new ASTNode[e.ScriptBytecode.Length];
                int i = 0;
                gFunctionName = functionName;
                foreach (var exp in e.ScriptBytecode)
                {
                    lines[i++] = Stringify(exp, ref index);
                }
                var bbRoot = CreateBasicBlock(lines);
                if (bbRoot is _Ok<BasicBlock> vbb)
                {
                    var bb = vbb.value;
                    var sbbb = new StringBuilder();
                    bb.GenerateCode(sbbb, null, null, null, null, 2);
                    var resultcode = PostGenerationRemoveUnusedLabel(sbbb.ToString());
                    stringBuilder.Append(resultcode);
                    referencedAddresses.Clear();
                } 
                if (bbRoot is Error || gFunctionName == debugging_function)
                {
                    if (bbRoot is Error err)
                        stringBuilder.Append($"// Failed to create basic block {err.message}" + "\n");
                    int index_line = 0;
                    foreach (var line in lines)
                    {
                        if (referencedAddresses.ContainsKey(line.line))
                        {
                            referencedAddresses.Remove(line.line);
                        }
                        stringBuilder.Append($"{index_line}\t{line.line}\t{line}\n");
                        index_line++;
                    }

                    if (referencedAddresses.Count > 0)
                    {
                        foreach (var pair in referencedAddresses)
                        {
                            stringBuilder.Append($"// WARN: Unresolved Reference: {GetRefString(pair.Key, pair.Value)}\n");
                        }
                        referencedAddresses.Clear();
                    }
                }
                stringBuilder.Append("\t}\n\n");
            }
        }

        stringBuilder.Append("}\n");
        import_table.Select(x => x.Value).ToList().ForEach(x => Output.WriteLine(x.ToString()));
        Output.WriteLine(stringBuilder.ToString());

        return anyExport;
    }


    void MarkAddress(uint addr, ReferenceType prefix, Dictionary<uint, ReferenceType>? refmap = null)
    {
        if (refmap == null) refmap = referencedAddresses;
        if (refmap.ContainsKey(addr))
        {
            refmap[addr] |= prefix;
        }
        else
        {
            refmap[addr] = prefix;
        }
    }

    ASTNode Stringify(KismetExpression exp, ref uint index, string context = "this") {
        uint line = index;
        index++;
        switch (exp) {
            case EX_PushExecutionFlow e:
                {
                    index += 4;
                    // ?
                    MarkAddress(e.PushingAddress, ReferenceType.LP);
                    return new PushFlowNode(line, e.PushingAddress);
                }
            case EX_PopExecutionFlow e:
                {
                    return new EndOfThreadNode(line);
                }
            case EX_PopExecutionFlowIfNot e:
                {
                    return new EndOfThreadIfNotNode(line, Stringify(e.BooleanExpression, ref index, "this"));
                }
            case EX_ComputedJump e:
                {
                    return new GotoComputeNode(line, Stringify(e.CodeOffsetExpression, ref index, "this"));
                }
            case EX_Jump e:
                {
                    index += 4;
                    MarkAddress(e.CodeOffset, ReferenceType.L);
                    MarkAddress(index, ReferenceType.L);
                    return Goto(line, (int) e.CodeOffset);
                }
            case EX_JumpIfNot e:
                {
                    index += 4;
                    MarkAddress(e.CodeOffset, ReferenceType.L);
                    var lret = IfNot(line, Stringify(e.BooleanExpression, ref index, "this"), (int) e.CodeOffset);
                    //MarkAddress(index, ReferenceType.C);
                    return lret;
                }
            case EX_LocalVariable e:
                {
                    if (context != "this")
                    {
                        throw new NotImplementedException("LocalVariable with non-this context");
                    }
                    //lines = new Lines("EX_" + e.Inst + " " + ToString(e.Variable));
                    index += 8;
                    return Line(line, Codes(ToString(e.Variable)));
                }
            case EX_LocalOutVariable e:
                {
                    if (context != "this")
                    {
                        throw new NotImplementedException("LocalVariable with non-this context");
                    }
                    //lines = new Lines("EX_" + e.Inst);
                    index += 8;
                    return Line(line, Codes(ToString(e.Variable)));
                }
            case EX_DefaultVariable e:
                {
                    index += 8;
                    return Line(line, Codes(ToString(e.Variable)));
                }
            case EX_InstanceVariable e:
                {
                    index += 8;
                    return Line(line, Codes("{0}.{1}", context, ToString(e.Variable)));
                }
            case EX_ObjToInterfaceCast e:
                {
                    index += 8;
                    return Line(line, Codes("interface_cast<{0}>({1})", CheckImport(e.ClassPtr), Stringify(e.Target, ref index, "this")));
                }
            case EX_InterfaceToObjCast e:
                {
                    index += 8;
                    return Line(line, Codes("object_cast<{0}>({1})", CheckImport(e.ClassPtr), Stringify(e.Target, ref index, "this")));
                }
            case EX_Let e:
                {
                    index += 8;
                    return new LetNode(line, Stringify(e.Variable, ref index, "this"), Stringify(e.Expression, ref index, "this"));
                }
            case EX_LetObj e:
                {
                    return new LetNode(line, Stringify(e.VariableExpression, ref index, "this"), Stringify(e.AssignmentExpression, ref index, "this"), "object");
                    // what is the difference?
                }
            case EX_LetBool e:
                {
                    return new LetNode(line, Stringify(e.VariableExpression, ref index, "this"), Stringify(e.AssignmentExpression, ref index, "this"), "bool");
                }
            case EX_LetWeakObjPtr e:
                {
                    return new LetNode(line, Stringify(e.VariableExpression, ref index, "this"), Stringify(e.AssignmentExpression, ref index, "this"), "weakobjptr");
                }
            case EX_LetValueOnPersistentFrame e:
                {
                    index += 8;
                    return new LetNode(line, ToString(e.DestinationProperty), Stringify(e.AssignmentExpression, ref index, "this"), "valueonpersistentframe");
                }
            case EX_StructMemberContext e:
                {
                    index += 8;
                    return Line(line, Codes("{0}:{1}", Stringify(e.StructExpression, ref index, "this"), ToString(e.StructMemberExpression)));
                }
            case EX_MetaCast e:
                {
                    index += 8;
                    //lines.Add(Stringify(e.TargetExpression, ref index));
                    return Line(line, Codes("meta_cast<{0}>({1})", CheckImport(e.ClassPtr), Stringify(e.TargetExpression, ref index, "this")));
                }
            case EX_DynamicCast e:
                {
                    index += 8;
                    //lines.Add(Stringify(e.TargetExpression, ref index));
                    return Line(line, Codes("dynamic_cast<{0}>({1})", CheckImport(e.ClassPtr), Stringify(e.TargetExpression, ref index, "this")));
                }
            case EX_PrimitiveCast e:
                {
                    // this is EX_Cast
                    index++;
                    switch (e.ConversionType) {
                        case ECastToken.InterfaceToBool:
                        {
                            // .$GetObject() is called
                            return Line(line, Codes("interface_cast<bool>({0})", Stringify(e.Target, ref index, "this")));
                        }
                        case ECastToken.ObjectToBool:
                        {
                            return Line(line, Codes("object_cast<bool>({0})", Stringify(e.Target, ref index, "this")));
                        }
                        case ECastToken.ObjectToInterface:
                        {
                            index += 8;
                            return Line(line, Codes("object_cast<{0}>({1}.$GetObject())", CheckImport(e.InterfaceClass), Stringify(e.Target, ref index, "this")));
                     
                        }
                        case ECastToken.DoubleToFloat:
                        {
                            return Line(line, Codes("float({0})", Stringify(e.Target, ref index, "this")));
                        }
                        case ECastToken.FloatToDouble:
                            {
                            return Line(line, Codes("double({0})", Stringify(e.Target, ref index, "this")));
                        }
                        default:
                            {
                            return Line(line, Codes("primitive_cast<(Unsupport)>({0})", Stringify(e.Target, ref index, "this")));
                        }
                    }
                }
            case EX_CallMath e:
                {
                    // call with default class as context
                    index += 8;
                    int nParams = e.Parameters.Length;
                    var parameters = new ASTNode[nParams];
                    // : stands for math function
                    for (int i = 0; i < nParams; i++)
                    {
                        parameters[i] = Stringify(e.Parameters[i], ref index, "this");
                    }
                    index++;
                    return new CallNode(line, CheckImport(e.StackNode), parameters, "$");
                }
            case EX_SwitchValue e:
                {
                    index += 6;
                    int nCases = e.Cases.Length;
                    var objlist = new object[nCases * 2 + 2];
                    objlist[0] = Stringify(e.IndexTerm, ref index, "this");
                    var format_str = "";
                    for (int i = 0; i < nCases; i++)
                    {
                        format_str += " case {" + (i * 2 + 1).ToString() + "}: {{ {" + (i * 2 + 2).ToString() + "} }}";
                        objlist[i * 2 + 1] = Stringify(e.Cases[i].CaseIndexValueTerm, ref index, "this");
                        index += 4;
                        objlist[i * 2 + 2] = Stringify(e.Cases[i].CaseTerm, ref index, "this");
                    }
                    format_str += " default: {{ {" + (nCases * 2 + 1).ToString() + "} }}";
                    objlist[nCases * 2 + 1] = Stringify(e.DefaultTerm, ref index, "this");

                    var l = Line(line, Codes("(switch ({0})" + format_str + ")", objlist));

                    // set index after the default case
                    index = e.EndGotoOffset;
                    return l;
                }
            case EX_Self e:
                {
                    return Line(line, Codes(context));
                }
            case EX_Context e:
                {
                    var obj = Stringify(e.ObjectExpression, ref index, context);
                    index += 4;
                    //lines.Add("SkipOffsetForNull = " + e.Offset);
                    index += 8;
                    var value = Stringify(e.ContextExpression, ref index, obj.ToString());
                    // TODO: this might be more complex rvalue?
                    return value;
                    // lines.Add("RValue = " + ToString(e.RValuePointer));
                }
            case EX_TextConst e:
                {
                    index++;
                    switch (e.Value.TextLiteralType) {
                        case EBlueprintTextLiteralType.LocalizedText:
                            {
                                //lines.Add(new Lines("SourceString = " + ReadString(e.Value.LocalizedSource, ref index)));
                                //lines.Add(new Lines("LocalizedKey = " + ReadString(e.Value.LocalizedKey, ref index)));
                                //lines.Add(new Lines("LocalizedNamespace = " + ReadString(e.Value.LocalizedNamespace, ref index)));
                                return Line(line, Codes("$tr(LocalizedSource: \"{0}\", LocalizedKey: \"{1}\", LocalizedNamespace: \"{2}\")", ReadString(e.Value.LocalizedSource, ref index), ReadString(e.Value.LocalizedKey, ref index), ReadString(e.Value.LocalizedNamespace, ref index)));
                            }
                        case EBlueprintTextLiteralType.InvariantText:
                            {
                                return Line(line, Codes("$tr(LocalizedSource: \"{0}\")", ReadString(e.Value.LocalizedSource, ref index)));
                            }
                        case EBlueprintTextLiteralType.LiteralString:
                            {
                                return Line(line, Codes("$tr(LocalizedSource: \"{0}\")", ReadString(e.Value.LiteralString, ref index)));
                            }
                        case EBlueprintTextLiteralType.StringTableEntry:
                            {
                                index += 8;
                                return Line(line, Codes("$trtable(TableId: \"{0}\", TableKey: \"{1}\")", ReadString(e.Value.StringTableId, ref index), ReadString(e.Value.StringTableKey, ref index)));
                            }
                        case EBlueprintTextLiteralType.Empty:
                        default:
                            {
                                return Line(line, Codes("\"\""));
                            }
                    }
                    
                }
            // TODO: add global import support
            case EX_ObjectConst e:
                {
                    index += 8;
                    return Line(line, Codes(CheckImport(e.Value)));
                }
            // TODO: use RyuCsharp to convert these
            case EX_VectorConst e:
                {
                    index += Asset.ObjectVersionUE5 >= ObjectVersionUE5.LARGE_WORLD_COORDINATES ? 24U : 12U;
                    return Line(line, Codes("vector3({0}, {1}, {2})", e.Value.X, e.Value.Y, e.Value.Z));
                }
            case EX_RotationConst e:
                {
                    index += Asset.ObjectVersionUE5 >= ObjectVersionUE5.LARGE_WORLD_COORDINATES ? 24U : 12U;
                    return Line(line, Codes("rotation({0}, {1}, {2})", e.Value.Pitch, e.Value.Yaw, e.Value.Roll));
                }
            case EX_TransformConst e:
                {
                    index += Asset.ObjectVersionUE5 >= ObjectVersionUE5.LARGE_WORLD_COORDINATES ? 80U : 40U;
                    return Line(line, Codes("transform(Rot=({0}, {1}, {2}, {3}) Pos=({4}, {5}, {6}) Scale=({7}, {8}, {9}))",
                        e.Value.Rotation.X, e.Value.Rotation.Y, e.Value.Rotation.Z, e.Value.Rotation.W,
                        e.Value.Translation.X, e.Value.Translation.Y, e.Value.Translation.Z,
                        e.Value.Scale3D.X, e.Value.Scale3D.Y, e.Value.Scale3D.Z));
                }
            case EX_CallMulticastDelegate e:
                {
                    index += 8;
                    //lines.Add("IsSelfContext = " + (Asset.GetClassExport().OuterIndex.Index == e.StackNode.Index));
                    var fdelegate = Stringify(e.Delegate, ref index, "this");
                    int nParams = e.Parameters.Length;
                    var parameters = new object[nParams + 1];
                    parameters[0] = fdelegate;
                    var format_str = "{0}!(" + getnparameter(nParams, 1) + ")"; // ! stands for multicast delegate
                    for (int i = 0; i < nParams; i++)
                    {
                        parameters[i + 1] = Stringify(e.Parameters[i], ref index, "this");
                    }
                    index++;
                    return Line(line, Codes(format_str, parameters));
                }
            case EX_LocalFinalFunction e:
                {
                    var fname = ToString(e.StackNode);
                    index += 8;
                    int nParams = e.Parameters.Length;
                    var parameters = new ASTNode[nParams];
                    //parameters[0] = context;
                    //parameters[1] = fname;
                    //var format_str = "{0}.{1}(" + getnparameter(nParams, 2) + ")";
                    for (int i = 0; i < nParams; i++)
                    {
                        parameters[i] = Stringify(e.Parameters[i], ref index, "this");
                    }
                    index++;
                    return new CallNode(line, $"{context}.{fname}", parameters, "");
                    //return Line(line, Codes(format_str, parameters));
                }
            // I guess this mean the function maybe remote?
            case EX_FinalFunction e:
                {
                    var fname = ToString(e.StackNode);
                    index += 8;
                    int nParams = e.Parameters.Length;
                    var parameters = new ASTNode[nParams];
                    //parameters[0] = context;
                    //parameters[1] = fname;
                    var format_str = "{0}.{1}(" + getnparameter(nParams, 2) + ")";
                    for (int i = 0; i < nParams; i++)
                    {
                        parameters[i + 0] = Stringify(e.Parameters[i], ref index, "this");
                    }
                    index++;
                    return new CallNode(line, $"{context}.{fname}", parameters, "");
                    //return Line(line, Codes(format_str, parameters));
                }
            case EX_LocalVirtualFunction e:
                {
                    var fname = e.VirtualFunctionName.ToString();
                    index += 12;
                    var nParams = e.Parameters.Length;
                    var parameters = new ASTNode[nParams + 0];
                    //parameters[0] = context;
                    //parameters[1] = fname;
                    //var format_str = "{0}.{1}(" + getnparameter(nParams, 2) + ")";
                    for (int i = 0; i < nParams; i++)
                    {
                        parameters[i + 0] = Stringify(e.Parameters[i], ref index, "this");
                    }
                    index++;
                    return new CallNode(line, $"{context}.{fname}", parameters, "");
                    //return Line(line, Codes(format_str, parameters));
                }
            case EX_VirtualFunction e:
                {
                    var fname = e.VirtualFunctionName.ToString();
                    index += 12;
                    var nParams = e.Parameters.Length;
                    var parameters = new ASTNode[nParams + 0];
                    //parameters[0] = context;
                    //parameters[1] = fname;
                    //var format_str = "{0}.{1}(" + getnparameter(nParams, 2) + ")";
                    for (int i = 0; i < nParams; i++)
                    {
                        parameters[i + 0] = Stringify(e.Parameters[i], ref index, "this");
                    }
                    index++;
                    return new CallNode(line, $"{context}.{fname}", parameters, "");
                    //return Line(line, Codes(format_str, parameters));
                }
            case EX_AddMulticastDelegate e:
                {
                    //lines = new Lines("EX_" + e.Inst);
                    //lines.Add(Stringify(e.Delegate, ref index));
                    //lines.Add(Stringify(e.DelegateToAdd, ref index));
                    return Line(line, Codes("{0}! += {1}", Stringify(e.Delegate, ref index, "this"), Stringify(e.DelegateToAdd, ref index, "this")));
                }
            case EX_RemoveMulticastDelegate e:
                {
                    // lines.Add(Stringify(e.Delegate, ref index));
                    // lines.Add(Stringify(e.DelegateToAdd, ref index));
                    return Line(line, Codes("{0}! -= {1}", Stringify(e.Delegate, ref index, "this"), Stringify(e.DelegateToAdd, ref index, "this")));
                }
            case EX_ClearMulticastDelegate e:
                {
                    return Line(line, Codes("{0}!.clear()", Stringify(e.DelegateToClear, ref index, "this")));
                }
            case EX_BindDelegate e:
                {
                    index += 12;
                    return Line(line, Codes("{0}!.Bind({1}, {2})", Stringify(e.Delegate, ref index, "this"), e.FunctionName, Stringify(e.ObjectTerm, ref index, "this")));
                }
            case EX_StructConst e:
                {
                    index += 8;
                    index += 4;
                    var format_str = "new " + CheckImport(e.Struct) + " {{ " + getnparameter(e.Value.Length, 0) + " }}";
                    var objlist = new object[e.Value.Length];
                    for (int i = 0; i < e.Value.Length; i++)
                    {
                        objlist[i] = Stringify(e.Value[i], ref index, "this");
                    }

                    index++;
                    /* why linkage is not recognized ?
                     * int32 Linkage;
                     * int32 UUID;
                     * FName ExecutionFunction;
                     * TObjectPtr<UObject> CallbackTarget
                     */
                    if (e.Struct.IsImport()) {
                        var s = e.Struct.ToImport(Asset);
                        if (s.ObjectName.ToString() == "LatentActionInfo" && s.ClassPackage.ToString() == "/Script/CoreUObject") {
                            if (e.Value.Length != 4) {
                                throw new Exception("Struct LatentActionInfo should have 4 members");
                            }
                            if (e.Value[0] is EX_SkipOffsetConst skip) {
                                if (e.Value[2] is EX_NameConst name) {
                                    if (e.Value[3] is EX_Self self) {
                                        // referencedAddresses.Add(new Reference(skip.Value, ReferenceType.Skip, name.Value.ToString()));
                                    } else {
                                        Console.Error.WriteLine("WARN: Unimplemented LatentActionInfo to other than EX_Self");
                                    }
                                } else {
                                    Console.Error.WriteLine("WARN: Expected EX_NameConst but found " + e.Value[2]);
                                }
                            } else {
                                Console.Error.WriteLine("WARN: Expected EX_SkipOffsetConst but found " + e.Value[0] + ", " + e.Value[1] + ", " + e.Value[2] + ", " + e.Value[3]);
                            }
                        }
                    }
                    return Line(line, Codes(format_str, objlist));
                    // break;
                }
            case EX_SetArray e:
                {
                    int nElements = e.Elements.Length;
                    var format_str = "{0} = new [" + getnparameter(nElements, 1) + "]";
                    var prop = Stringify(e.AssigningProperty, ref index, "this"); // no need to add
                    var objlist = new object[nElements + 1];
                    for (int i = 0; i < nElements; i++)
                    {
                        objlist[i + 1] = Stringify(e.Elements[i], ref index, "this");
                    }
                    objlist[0] = prop;
                    index++; // EX_EndArray
                    return Line(line, Codes(format_str, objlist));
                }
            case EX_SetSet e:
                {
                    int nElements = e.Elements.Length;
                    var format_str = "{0} = new Set {{ " + getnparameter(nElements, 1) + " }}";
                    var objlist = new object[nElements + 1];
                    objlist[0] = Stringify(e.SetProperty, ref index, "this");
                    index += 4;
                    for (int i = 0; i < nElements; i++)
                    {
                        objlist[i + 1] = Stringify(e.Elements[i], ref index, "this");
                    }
                    index++;
                    return Line(line, Codes(format_str, objlist));
                }
            case EX_SetMap e:
                {
                    var format_str = "{0} = new Map {{ " + getnpairparameter(e.Elements.Length, 1) + " }}";
                    index += 4;
                    var objlist = new object[e.Elements.Length * 2 + 1];
                    objlist[0] = Stringify(e.MapProperty, ref index, "this");
                    int i = 1;
                    foreach (var pair in Pairs(e.Elements)) {
                        objlist[i + 0] = Stringify(pair.Item1, ref index, "this");
                        objlist[i + 1] = Stringify(pair.Item2, ref index, "this");
                        i += 2;
                    }
                    index++;
                    return Line(line, Codes(format_str, objlist));
                }
            case EX_MapConst e:
                {
                    index += 8;
                    //lines.Add("KeyProperty: " + ToString(e.KeyProperty));
                    //lines.Add("ValueProperty: " + ToString(e.ValueProperty));
                    var format_str = "new Map<{0}, {1}> {{ " + getnpairparameter(e.Elements.Length, 2) + " }}";
                    var objlist = new object[e.Elements.Length * 2 + 2];
                    objlist[0] = ToString(e.KeyProperty);
                    objlist[1] = ToString(e.ValueProperty);
                    index += 4;
                    int i = 2;
                    foreach (var pair in Pairs(e.Elements)) {
                        objlist[i + 0] = Stringify(pair.Item1, ref index, "this");
                        objlist[i + 1] = Stringify(pair.Item2, ref index, "this");
                        i += 2;
                    }
                    index++;
                    return Line(line, Codes(format_str, objlist));
                }
            case EX_SoftObjectConst e:
                {
                    return Line(line, Codes("$SoftObject({0})", Stringify(e.Value, ref index, "this")));
                }
            case EX_ByteConst e:
                {
                    index++;
                    return Line(line, Codes("{0}b", e.Value));
                }
            case EX_IntConst e:
                {
                    //lines = new Lines("EX_" + e.Inst + " " + e.Value);
                    index += 4;
                    return Line(line, Codes("{0}", e.Value));
                }
            case EX_Int64Const e:
                {
                    index += 8;
                    return Line(line, Codes("{0}ll", e.Value));
                    //break;
                }
            case EX_UInt64Const e:
                {
                    index += 8;
                    return Line(line, Codes("{0}ull", e.Value));
                }
            case EX_FloatConst e:
                {
                    index += 4;
                    return Line(line, Codes("{0}f", e.Value));
                }
            case EX_DoubleConst e:
                {
                    index += 8;
                    return Line(line, Codes("{0}lf", e.Value));
                }
            case EX_NameConst e:
                {
                    index += 12;
                    return Line(line, Codes(":`{0}`:", e.Value.ToString()));
                }
            case EX_StringConst e:
                {
                    index += 1 + (uint) e.Value.Length;
                    return Line(line, Codes("\"{0}\"", e.Value));
                    //break;
                }
            case EX_UnicodeStringConst e:
                {
                    // todo: why 1 + ?
                    index += 1 + (uint) (e.Value.Length + 1) * 2;
                    return Line(line, Codes("\"{0}\"", e.Value));
                }
            case EX_ArrayConst e:
                {
                    index += 8; // InnerProperty
                    string format_str = "new " + ToString(e.InnerProperty) + " [" + getnparameter(e.Elements.Length, 0) + "]";
                    index += 4; // Num
                    var objlist = new object[e.Elements.Length];
                    for (int i = 0; i < e.Elements.Length; i++)
                    {
                        objlist[i] = Stringify(e.Elements[i], ref index, "this");
                    }
                    index++; // EX_EndArrayConst
                    return Line(line, Codes(format_str, objlist));
                }
            case EX_SkipOffsetConst e:
                {
                    // handled in LatentActionInfo struct instead
                    // referencedAddresses.Add(new Reference(e.Value, ReferenceType.Skip));
                    index += 4;
                    return Line(line, Codes("$skip({0})", e.Value));
                }
            case EX_Return e:
                {
                    return new ReturnNode(line, Stringify(e.ReturnExpression, ref index, "this"));
                }
            case EX_InterfaceContext e:
                {
                    return Line(line, Codes("{0}.$GetObject()", Stringify(e.InterfaceValue, ref index, context)));
                }
            case EX_ArrayGetByRef e:
                {
                    return Line(line, Codes("{0}[{1}]", Stringify(e.ArrayVariable, ref index, "this"), Stringify(e.ArrayIndex, ref index, "this")));
                }
            case EX_Tracepoint e:
                {
                    //lines = new Lines("EX_" + e.Inst);
                    return Line(line, Codes("$Tracepoint()"));
                }
            case EX_WireTracepoint e:
                {
                    return Line(line, Codes("$Tracepoint()"));
                }
            case EX_True:
            case EX_False:
                 return Line(line, Codes(exp.Inst.ToString().ToLower()));
            case EX_Nothing:
            case EX_NoObject:
            case EX_NoInterface:
                 return Line(line, Codes("null"));
            case EX_EndOfScript:
                {
                    return Line(line, Codes("// end"));
                }
            default:
                {
                    throw new NotImplementedException($"DBG missing expression {exp}");
                }
        }
        throw new NotImplementedException("Unreachable");
    }

    static IEnumerable<(KismetExpression, KismetExpression)> Pairs(IEnumerable<KismetExpression> input) {
        var e = input.GetEnumerator();
        try {
            while (e.MoveNext()) {
                var a = e.Current;
                if (e.MoveNext()) {
                    yield return (a, e.Current);
                }
            }
        } finally {
            (e as IDisposable)?.Dispose();
        }
    }

    static string ReadString(KismetExpression exp, ref uint index) {
        index++;
        switch (exp) {
            case EX_StringConst e:
                {
                    index += (uint) e.Value.Length + 1;
                    return e.Value;
                }
            case EX_UnicodeStringConst e:
                {
                    index += 2 * ((uint) e.Value.Length + 1);
                    return e.Value;
                }
            default:
                Console.Error.WriteLine("WARN: ReadString called on non-string");
                return "ERR";
        }
    }

    string ToString(KismetPropertyPointer pointer) {
        if (pointer.Old != null) {
            return ToString(pointer.Old);
        }
        if (pointer.New != null) {
            return ToString(pointer.New.Path);
        }
        throw new Exception("Unreachable");
    }

    string ToString(FPackageIndex index) {
        if (index.IsNull()) {
            return "null";
        } else if (index.IsExport()) {
            return index.ToExport(Asset).ObjectName.ToString();
            //return $"export {getChain(index.ToExport(Asset).OuterIndex)}{index.ToExport(Asset).ObjectName}";
        } else if (index.IsImport())
        {
            return index.ToImport(Asset).ObjectName.ToString();
            // return $"import {getChain(index.ToImport(Asset).OuterIndex)}{index.ToImport(Asset).ObjectName}";
        }
        throw new Exception("Unreachable");
    }

    string ToStringImport(FPackageIndex index)
    {
        List<string> getChain(FPackageIndex child)
        {
            if (child.IsNull())
            {
                return new List<string>();
            }
            if (child.IsImport())
            {
                var a = child.ToImport(Asset);
                var chain = getChain(a.OuterIndex);
                chain.Add(a.ObjectName.ToString());
                return chain;
            }
            if (child.IsExport())
            {
                var a = child.ToExport(Asset);
                var chain = getChain(a.OuterIndex);
                chain.Add(a.ObjectName.ToString());
                return chain;
            }
            throw new NotImplementedException("Unreachable");

        }
        if (index.IsNull())
        {
            return "null";
        }
        else
        {
            if (index.IsImport())
            {
                var longname = string.Join(".", getChain(index.ToImport(Asset).OuterIndex));
                return longname;
            } return "<ERROR>";
           
        }
    }
    static void PrintIndent(TextWriter Output, int indent, string str, string prefix = "") {
        Output.WriteLine((indent == 0 ? prefix : "").PadRight((indent + 2) * 4) + str);
    }

    static string ToString(FName[] arr) {
        if (arr.Length == 0) {
            return "[]";
        } else
        {
            if (arr.Length == 1) {
                return arr[0].ToString();
            }
        }
        return "[" + String.Join(",", (object[]?)arr) + "]";
    }
}
