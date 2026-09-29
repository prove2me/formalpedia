-- Prove2me | Theorems.Thm_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology
-- name    : AddSubgroup.exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/1a9955a3-85a2-52d0-bf01-c76d3c3b1325
-- title:
--   Uniform bound for product weights over a discrete subgroup
-- statement:
--   Let $r$ be a natural number and let $\Gamma$ be an additive subgroup of $\mathbb{R}^r$ (functions $\mathrm{Fin}\,r \to \mathbb{R}$) whose induced subspace topology is discrete. The assertion is that there exists a real constant $K$ with the following property: for every $y \in \mathbb{R}^r$ and every finite set $F$ of points of $\mathbb{R}^r$ all of whose elements lie in $\Gamma$, $$\sum_{x \in F} \prod_{k} \bigl( (1 + |y_k + x_k|)^{-1} \bigr)^{2} \le K,$$ the product being over the $r$ coordinates. Thus the constant is uniform both in the translation parameter $y$ and in the finite subset $F$ of $\Gamma$; nothing is asserted about $\Gamma$ beyond discreteness (in particular it need not have full rank, and $K$ is not claimed to be positive or explicit). Since all terms are nonnegative, the bound on all finite partial sums is equivalent to summability over $\Gamma$ of the family $x \mapsto \prod_k (1+|y_k+x_k|)^{-2}$ with sum at most $K$, uniformly in $y$.
--
--   This is the standard lattice-point estimate showing that sums of a product weight of Poisson type, taken over a discrete subgroup of $\mathbb{R}^r$, are bounded uniformly in the translate. It is used to obtain uniform summability and bounds for the fibre terms and fibre coefficients attached to a winding datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AddSubgroup.exists_forall_sum_prod_inv_one_add_abs_sq_le_of_discreteTopology
    {r : ℕ} (Γ : AddSubgroup (Fin r → ℝ)) [DiscreteTopology Γ] :
    ∃ K : ℝ, ∀ (y : Fin r → ℝ) (F : Finset (Fin r → ℝ)), (↑F : Set (Fin r → ℝ)) ⊆ Γ →
      ∑ x ∈ F, ∏ k, (1 + |y k + x k|)⁻¹ ^ 2 ≤ K := by sorry
