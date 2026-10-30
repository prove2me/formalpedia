-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_polar_endpoint_winding_bound
-- name    : BirkhoffGlobalSection.polar_endpoint_winding_bound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:03:33.490121+00:00
-- url     : https://prove2.me/theorems/53b315c0-e8a5-40a3-b631-a90d61248823
-- title:
--   Polar endpoint winding bound without smoothness assumptions
-- statement:
--   Let $\varphi:[0,1]\to SL(2,\mathbb R)$ admit a continuous polar-angle lift $\alpha$, normalized by $\alpha(0)=0$, so that $\varphi(t)=R(\alpha(t))P(t)$ with $P(t)$ symmetric positive definite. Write $V(g)$ for the graph unitary and $a(V)$ for the sum of its eigenvalue arguments in $(0,2\pi]$. If
--
--   $$4\pi+a(V(\varphi(1)))\le2\alpha(1),$$
--
--   then every continuous vector-angle lift of $\varphi$ advances by more than $2\pi$:
--
--   $$\inf\{d:d\in I(\varphi)\}>1$$
--
--   in the pointwise sense $d>1$ for every $d$ in its winding interval $I(\varphi)$. No differentiability of $\varphi$ is required. This exposes the weaker internal lemma already established by Mazecto's accepted proof, allowing reuse for Hamiltonians with only two derivatives. The formal conclusion is the pointwise inequality, without a separate claim about the strict infimum.
-- source:
--   Mazecto, accepted submission ff037411-3ebd-4447-9fe1-41adddefd354, internal theorem polar_angle_windingInterval_gt_one′ in https://prove2.me/theorems/f8db6526-c2d2-4998-b391-ae3e559b61b0. This is the existing internal statement, exposed without the unused smoothness and initial-matrix assumptions of the published wrapper. HWZ, Ann. Math.148(1998), equations (3.45)-(3.46), https://doi.org/10.2307/120994.

import Definitions.Def_HryniewiczCriterion_GraphAngle

theorem BirkhoffGlobalSection.polar_endpoint_winding_bound (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (α : ℝ → ℝ) (hα : HryniewiczCriterion.IsPolarAngleLift φ α)
    (h : 4 * Real.pi + HryniewiczCriterion.eigenAngleSum
      (HryniewiczCriterion.graphUnitary2 (φ 1)) ≤ 2 * α 1) :
    ∀ d ∈ HryniewiczCriterion.windingInterval φ, 1 < d := by sorry
