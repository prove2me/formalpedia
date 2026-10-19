-- Prove2me | Theorems.Thm_FlatlyFoliated_orthogonal_spherical_average
-- name    : FlatlyFoliated.orthogonal_spherical_average
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T18:40:31.363253+00:00
-- url     : https://prove2.me/theorems/ce4a0c0e-cb5c-4579-86ca-d5e750626b75
-- title:
--   Orthogonal probability representation of spherical averages
-- statement:
--   There is one probability distribution on the closed operator-norm unit ball of linear endomorphisms of $\mathbb R^3$, concentrated on orthogonal transformations, with the identity transformation in its topological support, such that for every continuous function $g$ and every $x\in\mathbb R^3$,
--   $$\int g(Ax)\,d\nu(A)=\overline g(x).$$
--   Here $\overline g$ is the normalized surface average on the sphere of radius $\lVert x\rVert$, including its value $g(0)$ at the origin. This is the compact-group averaging representation in equation (77) of the source, stated using continuous linear operators to give the parameter space its standard finite-dimensional topology. Normalized Haar measure on the orthogonal group, pushed into the operator ball, gives the required distribution. No differentiability, field equation, positivity or behavior at infinity is assumed.
--
--   This helper is used by the Hessian-barycenter reduction: the reduction proves smooth differentiation under the compact average, orthogonal invariance of the trace and Hessian norm, the Hessian moments and the support property. Only the measure-theoretic representation of the spherical average remains here.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, Section 5, equations (75)–(77). https://arxiv.org/html/1911.00967v2

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped Topology
open MeasureTheory Metric

theorem FlatlyFoliated.orthogonal_spherical_average :
    ∃ ν : Measure {A : FlatlyFoliated.R3 →L[ℝ] FlatlyFoliated.R3 // A ∈ closedBall 0 1},
      IsProbabilityMeasure ν ∧
      (∀ᵐ A ∂ν, ∃ T : FlatlyFoliated.R3 ≃ₗᵢ[ℝ] FlatlyFoliated.R3,
        A.1 = T.toContinuousLinearEquiv.toContinuousLinearMap) ∧
      (⟨ContinuousLinearMap.id ℝ FlatlyFoliated.R3, by simp⟩ ∈ ν.support) ∧
      ∀ (g : FlatlyFoliated.R3 → ℝ), Continuous g → ∀ x,
        (∫ A, g (A.1 x) ∂ν) = FlatlyFoliated.sphSymmetrization g x := by sorry
