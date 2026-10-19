-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_affine_lower_bound
-- name    : BudgetedAffine.NetworkGap.affine_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:37.346175+00:00
-- url     : https://prove2.me/theorems/131e0b0f-145f-45dc-8470-5f5a4b73089b
-- title:
--   App. D, p. 37 — every feasible affine solution stocks ≥ m/2 − 1 on J₂, so z_Aff ≥ m/2 − 1
-- statement:
--   Consider the family of lot-sizing instances (7.2) with $m=2k$ nodes. Every feasible affine solution $(x,\,y(h)=Ph+q)$ satisfies
--   $$\sum_{j\in J_2}x_j\ \ge\ \frac m2-1=k-1,$$
--   and consequently every affine objective value $t$ (a number with $\sum_i c_ix_i+\sum_{ij}d_{ij}y_{ij}(h)\le t$ for all $h\in\mathcal U$, for some feasible affine solution) satisfies $t\ge m/2-1$:
--   $$z_{Aff}(\mathcal U)\ \ge\ \sum_{j=1}^m c_jx_j=\sum_{j\in J_2}x_j\ \ge\ \frac m2-1 .$$
--
--   This is the lower half of the affine value in Lemma 7.1.
--
--   **Formalization Note** The statement holds for every $k$ (for $k\le1$ it reduces to $x\ge0$, resp. to the non-negativity of the cost), so no hypothesis on $k$ is added. Lean indices are 0-based; $m/2-1$ is the real number $k-1$, never a natural-number subtraction.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, App. D, from "Therefore, Σ_{j∈J2} xj + Σ_{j∈J2} qℓj ≥ m/2" to "zAff ≥ Σ cjxj = Σ_{j∈J2} xj ≥ m/2 − 1", p. 37

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance

namespace BudgetedAffine.NetworkGap

/-- App. D, p. 37: every feasible affine solution `(x, y(h) = P h + q)` of the family (7.2)
stocks at least `m/2 − 1 = k − 1` units on `J₂`, and hence `k − 1` is a lower bound for
the objective value of every affine solution: `z_Aff(U) ≥ m/2 − 1`. -/
theorem affine_lower_bound (k : ℕ) :
    (∀ (x : Node k → ℝ) (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ),
        (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q) →
          (k : ℝ) - 1 ≤ ∑ j, x (Sum.inr j)) ∧
      (k : ℝ) - 1 ∈ lowerBounds (lotSizingFamily k).affineValues := by sorry

end BudgetedAffine.NetworkGap
