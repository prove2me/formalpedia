-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_affine_cover_bound
-- name    : BudgetedAffine.NetworkGap.affine_cover_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:29.540981+00:00
-- url     : https://prove2.me/theorems/cc7d08b4-1a40-4fc4-be7e-08edf0f431e8
-- title:
--   App. D, pp. 36–37 — every feasible affine solution has x_j + q_{ℓj} ≥ 1 for ℓ ∈ J₁, j ∈ J₂
-- statement:
--   Consider the family of lot-sizing instances (7.2) with $m=2k$ nodes and $k\ge 2$, and let $(x,\,y(h)=Ph+q)$ be any feasible affine solution. Then for every $\ell\in J_1$ and every $j\in J_2$,
--   $$x_j+q_{\ell j}\ \ge\ 1 .$$
--
--   The bound comes from the scenario in which every node of $J_1$ except $\ell$ and the single node $j$ of $J_2$ have unit demand; together with (D.3) it is the step that turns the rigidity of affine policies into a cost on $J_2$.
--
--   **Formalization Note** The paper writes "for any $j\in J_1$ and for any $\ell\in J_2$"; the roles are swapped there (the scenario it uses has $\ell\in J_1$, $j\in J_2$, and $q_{\ell j}$ is only defined for $\ell\in J_1$, $j\in J_2$). The statement uses $\ell\in J_1$, $j\in J_2$. The hypothesis $k\ge 2$ is added and necessary: for $k=1$ the feasible affine solution $x=(1,0)$, $y(h)=h_{J_2}$ has $x_{J_2}+q=0<1$. Lean indices are 0-based.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, App. D, from "Now fix ℓ ∈ J1 and j ∈ J2" (p. 36) to "xj + qℓj ≥ 1" (p. 37)

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance

namespace BudgetedAffine.NetworkGap

/-- App. D, pp. 36–37: for `k ≥ 2`, every feasible affine solution `(x, y(h) = P h + q)` of the
family (7.2) satisfies `x_j + q_{ℓj} ≥ 1` for every `ℓ ∈ J₁` and `j ∈ J₂`. -/
theorem affine_cover_bound (k : ℕ) (hk : 2 ≤ k) (x : Node k → ℝ)
    (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (hfeas : (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q)) :
    ∀ ℓ j : Fin k, 1 ≤ x (Sum.inr j) + q (ℓ, j) := by sorry

end BudgetedAffine.NetworkGap
