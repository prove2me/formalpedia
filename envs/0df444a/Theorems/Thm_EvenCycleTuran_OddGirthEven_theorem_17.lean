-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_theorem_17
-- name    : EvenCycleTuran.OddGirthEven.theorem_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:35.172803+00:00
-- url     : https://prove2.me/theorems/512d6f7c-a531-40bf-81a4-67a48f1cd1e6
-- title:
--   Theorem 17 — two-sided bounds for odd cycles with even-cycle exclusion
-- statement:
--   Let $k>l\ge2$ be fixed integers. Among all graphs $G$ on $n$ vertices containing none of $C_3,C_4,\ldots,C_{2l},C_{2k}$, let $\operatorname{ex}(n,C_{2l+1},\mathcal C_{2l}\cup\{C_{2k}\})$ be the maximum number of unlabelled copies of $C_{2l+1}$. As $n$ tends to infinity,
--
--   $$\operatorname{ex}(n,C_{2l+1},\mathcal C_{2l}\cup\{C_{2k}\})=\Omega\bigl(n^{1+1/(2k+1)}\bigr)$$
--
--   and
--
--   $$\operatorname{ex}(n,C_{2l+1},\mathcal C_{2l}\cup\{C_{2k}\})=O\bigl(n^{1+l/(l+1)}\bigr).$$
--
--   The result gives both a constructive growth lower bound and a subquadratic upper bound for this generalized Turán number. The exponents refer to real powers, with $k,l$ fixed before $n$ grows.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 7, Theorem 17; restated p. 27, §6.2

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

open Filter Asymptotics

namespace EvenCycleTuran.OddGirthEven

/-- Theorem 17, p. 7: two-sided asymptotic bounds for odd cycles. -/
theorem theorem_17 (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) + 1 / (2 * (k : ℝ) + 1))) =O[atTop]
        (fun n : ℕ => (EvenCycleTuran.C4Count.exCyc n (SimpleGraph.cycleGraph (2 * l + 1))
          (Set.Icc 3 (2 * l) ∪ {2 * k}) : ℝ)) ∧
    (fun n : ℕ => (EvenCycleTuran.C4Count.exCyc n (SimpleGraph.cycleGraph (2 * l + 1))
          (Set.Icc 3 (2 * l) ∪ {2 * k}) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) + (l : ℝ) / ((l : ℝ) + 1))) := by sorry

end EvenCycleTuran.OddGirthEven
