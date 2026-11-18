-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
-- name    : EdgeSublinearMWIS.Main.realizer_native_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T21:06:30.282088+00:00
-- url     : https://prove2.me/theorems/80aa782e-c7f4-4bc4-9257-d352c639ff64
-- title:
--   Finite stack execution of a binary-tree realizer
-- statement:
--   Let $f$ be a function on finite binary strings and let $R$ be a finite binary-tree program realizing $f$, with its operational charge $t_R(x)$. There is one finite deterministic stack program $P$ and a constant $K>0$, independent of the input, such that for every binary input $x$,
--
--   $$P(x)=f(x),\qquad T_P(x)\le K\bigl(t_R(x)+|x|+|f(x)|+1\bigr).$$
--
--   The stack program has finite control and finite stack alphabets and finishes with the prescribed output and empty auxiliary stacks. This compiler interface allows the rational preprocessing routines in the weighted reduction to be implemented in the same operational model as the unweighted solver.
-- source:
--   Bonnet–Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf, p.20 weighted reduction and p.2 bit-complexity paragraph; implementation lemma for finite-program composition, using the published OAI.ThreeMachine.StackCompiler compiler (platform theorem OAI.ThreeMachine.main_theorem, 1120d537), followed by a direct finite-control simulation.

import Definitions.Def_OAIThreeMachineSched02
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main

theorem EdgeSublinearMWIS.Main.realizer_native_program (f : List Bool → List Bool) (R : Realizer f) :
    ∃ (P : EdgeSublinearMWIS.Main.Program) (K : ℕ),0<K ∧ ∀input,
      Runs P input (f input) (K*(R.time input+input.length+(f input).length+1)) := by sorry
