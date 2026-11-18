-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_polynomial_context_program
-- name    : EdgeSublinearMWIS.Main.polynomial_context_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T22:31:41.50469+00:00
-- url     : https://prove2.me/theorems/82c8dd81-220e-4541-aada-72c7317a4bb5
-- title:
--   Polynomial context-preserving composition of finite stack programs
-- statement:
--   Let $F$ and $G$ be finite binary-tree routines whose operational charges and output volumes are polynomial in their input volumes. Let $U$ be any fixed finite deterministic stack program. There is one finite stack program $P$ and two fixed polynomials $T$ and $Q$ such that whenever
--
--   $$F(x)=\operatorname{prefix}(c)\,z,\qquad U(z)=y\text{ within }t\text{ steps},$$
--
--   one has
--
--   $$P(x)=G(\operatorname{prefix}(c)\,y)\text{ within }T(t+|x|+1)\text{ steps},\qquad |z|+1\le Q(|x|+1).$$
--
--   Here the context prefix consists of $|c|$ true bits, a false delimiter and then $c$. All programs have finite control and finite stack alphabets, and execution ends with empty auxiliary stacks. This interface implements a solver subcall while preserving the data needed to decode its answer in the original labels.
-- source:
--   Bonnet–Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf, Section 3.1 pp.7–8, proof of Lemmas 7–8 (induced subcalls), Section 5.3 pp.18–19 (charged subcalls), and Section 6 p.20 (weighted reduction). Implementation lemma: actual finite-program context preservation, using the proved EdgeSublinearMWIS.Main.realizer_native_program compiler.

import Definitions.Def_OAIThreeMachineSched02
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main

theorem EdgeSublinearMWIS.Main.polynomial_context_program (f g : List Bool → List Bool) (R : Realizer f) (S : Realizer g)
    (hR : ∃ C q : ℕ,0< C ∧ ∀x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q)
    (hS : ∃ C q : ℕ,0< C ∧ ∀x,S.time x≤ C*(volume x+1)^q ∧ volume (g x)≤ C*(volume x+1)^q)
    (U : EdgeSublinearMWIS.Main.Program) :
    ∃ (P : EdgeSublinearMWIS.Main.Program) (time size : Polynomial ℕ),
      ∀ (input ctx middle output : List Bool) (T : ℕ),
        f input=(List.replicate ctx.length true++false::ctx)++middle → Runs U middle output T →
        ∃s,Runs P input (g ((List.replicate ctx.length true++false::ctx)++output)) s ∧
          s≤ time.eval (T+input.length+1) ∧ middle.length+1≤ size.eval (input.length+1) := by sorry
