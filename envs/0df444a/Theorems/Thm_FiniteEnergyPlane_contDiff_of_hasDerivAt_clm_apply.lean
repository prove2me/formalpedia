-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiff_of_hasDerivAt_clm_apply
-- name    : FiniteEnergyPlane.contDiff_of_hasDerivAt_clm_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T23:10:30.159905+00:00
-- url     : https://prove2.me/theorems/0d6cd977-e98d-47eb-8858-9809ac06ffc8
-- title:
--   Solutions of linear ODEs with smooth operator coefficients are smooth
-- statement:
--   Let $E$ be a real normed space and let $A:\mathbb{R}\to\mathcal{L}(E,E)$ be a $C^\infty$ map into the bounded linear operators on $E$. If $x:\mathbb{R}\to E$ is differentiable everywhere with
--   $$x'(t)=A(t)\,x(t)\qquad\text{for all }t\in\mathbb{R},$$
--   then $x$ is $C^\infty$.
--
--   This is the regularity statement for linear differential equations with smooth coefficients. It is used to show that limits of approximate eigenfunctions of an asymptotic operator are smooth (`FiniteEnergyPlane.exists_subseq_tendstoUniformly_isLoopEigen`).
--
--   **Formalization Note** $A$ is `ℝ → E →L[ℝ] E` with `ContDiff ℝ ∞ A`; the equation is `∀ t, HasDerivAt x (A t (x t)) t`.
-- source:
--   Standard (linear ODE regularity); used for C. Wendl, Lectures on Symplectic Field Theory, Section 4.8

import Mathlib

open scoped ContDiff

namespace FiniteEnergyPlane

/-- If `A : ℝ → (E →L[ℝ] E)` is smooth and `x' = A(t) x` on `ℝ`, then `x` is smooth. -/
theorem contDiff_of_hasDerivAt_clm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (x : ℝ → E)
    (hx : ∀ t, HasDerivAt x (A t (x t)) t) : ContDiff ℝ ∞ x := by
  sorry

end FiniteEnergyPlane
