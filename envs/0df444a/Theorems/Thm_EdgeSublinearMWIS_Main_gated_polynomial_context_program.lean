-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_gated_polynomial_context_program
-- name    : EdgeSublinearMWIS.Main.gated_polynomial_context_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:34:19.454191+00:00
-- url     : https://prove2.me/theorems/8a2d0099-d911-4374-9a1a-c73d7f428811
-- title:
--   Polynomial gated native calls with preserved context
-- statement:
--   Let $U$ be any finite deterministic stack program, and let $f$ and $g$ be preprocessing and postprocessing functions realized by fixed polynomial-time stack routines with polynomial output size. There is one finite program $P$ and a fixed polynomial $p$ implementing a conditional native call.
--
--   If preprocessing gives a false flag followed by a word $z$, the program outputs $g(z)$ within
--
--   $$p(2|z|+|x|+4)$$
--
--   actual steps. If preprocessing gives a true flag, a self-delimiting context $c$, and a subprogram input $y$, and $U$ outputs $z$ within $T$ steps, then $P$ preserves the context and outputs $g(\operatorname{prefix}(c)z)$ within
--
--   $$p(T+4|c|+2|y|+|x|+8)$$
--
--   actual steps. The prefix consists of a unary context-length header, a false delimiter and the context itself. This provides the conditional calls needed by bounded graph-algorithm loops, while completed states can be carried through the same finite program.
-- source:
--   Supporting finite-program implementation of the repeated calls in Bonnet–Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf, Lemma 8 proof, pp.7–8. The statement isolates the native gated-call compiler and its actual execution bounds.

import Definitions.Def_OAIThreeMachineSched02
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main

theorem EdgeSublinearMWIS.Main.gated_polynomial_context_program (f g : List Bool → List Bool) (R : Realizer f) (S : Realizer g)
    (hR : ∃C q : ℕ,0< C ∧ ∀x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q)
    (hS : ∃C q : ℕ,0< C ∧ ∀x,S.time x≤ C*(volume x+1)^q ∧ volume (g x)≤ C*(volume x+1)^q)
    (U : Program) :
    ∃ (P : Program) (time : Polynomial ℕ),
      (∀input output : List Bool,f input=false::output →
        ∃s,Runs P input (g output) s ∧ s≤ time.eval (2*output.length+input.length+4)) ∧
      (∀(input ctx middle output : List Bool) (T : ℕ),
        f input=true::((List.replicate ctx.length true++false::ctx)++middle) → Runs U middle output T →
        ∃s,Runs P input (g ((List.replicate ctx.length true++false::ctx)++output)) s ∧
          s≤ time.eval (T+4*ctx.length+2*middle.length+input.length+8)) := by sorry
