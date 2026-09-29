-- Prove2me | Theorems.Thm_BassokSubstitution_order_up_to_base_stock
-- name    : BassokSubstitution.order_up_to_base_stock
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:34:48.020433+00:00
-- url     : https://prove2.me/theorems/9c57235a-e3fe-41b7-a424-075993a71f84
-- title:
--   Theorem 1 — order up to $y^*$ when the starting inventory is below $y^*$
-- statement:
--   Consider the model with Assumptions 1–3 and $b \ge 0$, with unit costs satisfying $s_i < c_i < p_i + \pi_i$ for every product $i$, and independent nonnegative demands with densities and finite means whose laws charge every nonempty open interval of $[0,\infty)$. Then there is a base-stock vector $y^* \ge 0$ such that for every starting inventory $x$ with $0 \le x \le y^*$ (componentwise), the optimal inventory level after ordering is $y^*$:
--   $$\bar y(x) = y^*,$$
--   that is, $y^*$ maximizes $P(x, \cdot)$ over $\{y : y \ge x\}$, and it is the only maximizer.
--
--   This is the order-up-to (base-stock) structure of the optimal policy: whenever no product is overstocked relative to $y^*$, every product is brought up to its base-stock level.
--
--   **Formalization Note.** The paper writes $\vec x < \vec y^*$; it is read componentwise as $x \le y^*$ (the statement holds a fortiori for strict inequalities, and the paper's proof says "whenever $\vec x < \vec y^*$"). "$\bar y(x) = y^*$" presupposes one optimal level, so uniqueness of the maximizer is part of the claim. The paper's proof uses, without stating them: $s_i < c_i < p_i + \pi_i$ (the partial derivatives are positive near $y = 0$ and negative for large $y$), independence and densities, finite means, and uniqueness of the optimal level, which is secured here by the full-support hypothesis. The paper's proof also asserts $\partial P/\partial y_i = 0$ at $y^*$; this is not part of the statement, since a coordinate of $y^*$ can sit at $0$.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 635, Theorem 1

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Theorem 1: there is a base-stock vector `y* ≥ 0` such that for every starting inventory
`0 ≤ x ≤ y*` the optimal inventory level after ordering is `y*`: `y*` maximizes `P(x, ·)`
over `{y | x ≤ y}` and is the only maximizer. -/
theorem order_up_to_base_stock {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (hcost : ∀ i, M.s i < M.c i ∧ M.c i < M.p i + M.penalty i)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (hsupp : FullSupport ν) :
    ∃ ystar : Fin N → ℝ, 0 ≤ ystar ∧
      ∀ x : Fin N → ℝ, 0 ≤ x → x ≤ ystar →
        IsMaxOn (M.profit (Measure.pi ν) x) {y | x ≤ y} ystar ∧
          ∀ ybar : Fin N → ℝ, x ≤ ybar →
            IsMaxOn (M.profit (Measure.pi ν) x) {y | x ≤ y} ybar → ybar = ystar := by sorry

end BassokSubstitution
