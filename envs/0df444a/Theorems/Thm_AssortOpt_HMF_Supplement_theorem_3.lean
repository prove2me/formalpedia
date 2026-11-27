-- Prove2me | Theorems.Thm_AssortOpt_HMF_Supplement_theorem_3
-- name    : AssortOpt.HMF.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:19:56.779172+00:00
-- url     : https://prove2.me/theorems/f532165b-262a-45eb-9032-646fc8a64c93
-- title:
--   Theorem 3 — exponential independent inclusion earns at least 1/e of every budget-additive mechanism
-- statement:
--   Let $D$ be any finite list distribution, let $r_j\ge0$ be fixed item prices, and let $w_j\ge0$ and $B\in[0,1]$ define the budget-additive mechanism $x^B$ of Definition 17. Include each item $j$ independently with probability $1-e^{-w_j}$, independently of the buyer. Then
--   $$\mathbb E_S[\mathsf{REV}[S]]\ge\frac1e\mathsf{REV}[x^B].$$
--   The guarantee concerns this particular product distribution of assortments for every real nonnegative weight vector, including weights larger than one or the budget. It bounds the revenue loss from using assortments rather than budget-additive lotteries.
--
--   Differences from the source:
--   - encoding: items N={1,…,n} and a finite list distribution → 0-based Fin n and the published ListDist with strictly positive support of Nodup lists; reason: the same finite distributions, including empty lists and n=0, are represented
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 24, Theorem 3

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_BudgetRandom

namespace AssortOpt.HMF.Supplement

theorem theorem_3 {n : ℕ} (D : ListDist n) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (B : ℝ) (hB : B ∈ Set.Icc (0 : ℝ) 1) :
    (1 / Real.exp 1) * revMech D r (budgetMech w B) ≤
      revIndependent D r (expInclusion w) := by sorry

end AssortOpt.HMF.Supplement
