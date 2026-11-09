-- Prove2me | Theorems.Thm_ChoresTIE197_Main_theorem_B_4
-- name    : ChoresTIE197.Main.theorem_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:19:44.519179+00:00
-- url     : https://prove2.me/theorems/a368355f-5055-41e3-9f07-b6fcb797ab5e
-- title:
--   Theorem B.4 — two-agent truthful 4/3-MMS mechanism
-- statement:
--   For two agents under the positive-MMS standing convention, the actual Mechanism 3 is truthful in expectation, ex-ante envy-free and ex-post $4/3$-MMS:
--   $$\mathbb E[c_i(X_i(c))]\le\mathbb E[c_i(X_i(\widehat c_i,c_{-i}))],\quad
--   \mathbb E[c_i(X_i(c))]\le\mathbb E[c_i(X_j(c))],\quad
--   c_i(X_i)\le\frac43\mu_i\text{ for every supported }X.$$
--   The same public procedure handles every admissible report and alternative report. One exact rational-input bit sampler implements its allocation law and has polynomially bounded running time on every tape. Nominees are swapped in the distinct case, while residual parts share one fair coin.
--
--   Differences from the source:
--   - encoding: finite labelled agents and chores with complete ordered partitions and public tie breaking → Fin indices starting at zero, nonnegative real singleton tables, PMFs on owner maps, index ties; reason: every finite source instance and complete allocation is represented, including empty bundles
--   - encoding: standing positive-MMS convention on p.7 → each nonnegative cost row has positive total cost; reason: for n greater than zero on finite nonnegative instances, positive total cost and positive MMS are equivalent; individual zero item costs remain allowed
--   - reading: Mechanism 3 runs in polynomial time → one exact rational-input fair-bit program with a polynomial bound on every tape, together with real-input guarantees; reason: the proof uses deterministic polynomial routines and one fair coin, so its stronger bounded runtime is retained
--   - encoding: constructive partition or matching choices left to a public implementation → the explicitly defined public numeric choices and greedy routines; reason: these choose only from operational membership or positive-edge conditions, never from the desired fairness or incentive conclusions
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem B.4, printed p.37, PDF p.37; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Families

open Finset Classical
open scoped NNReal ENNReal
noncomputable section

namespace ChoresTIE197.Main

theorem theorem_B_4 :
    PolyBoundedSampler (fun n m k c => n = 2 ∧ 0 < m ∧ k = 0 ∧ Positive c) twoFamily ∧
    ∀ m [NeZero m],
      TIEOn Positive (@mechanism3 m _) ∧ EFOn Positive (@mechanism3 m _) ∧
      MMSOn Positive (4/3:ℝ) (@mechanism3 m _) := by sorry

end ChoresTIE197.Main
