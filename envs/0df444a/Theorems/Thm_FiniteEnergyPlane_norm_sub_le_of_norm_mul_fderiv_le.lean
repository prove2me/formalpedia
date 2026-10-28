-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_sub_le_of_norm_mul_fderiv_le
-- name    : FiniteEnergyPlane.norm_sub_le_of_norm_mul_fderiv_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:07:15.084185+00:00
-- url     : https://prove2.me/theorems/c3ac2274-20ec-4da7-a3cd-32f6614332f3
-- title:
--   Oscillation on circles from a weighted gradient bound near the origin
-- statement:
--   Let $E$ be a real normed space, $R,\eta\in\mathbb{R}$ and $f:\mathbb{C}\to E$ a map that is differentiable at every $z$ with $0<|z|<R$ and satisfies
--   $$|z|\,\|Df(z)\|\le\eta\qquad(0<|z|<R),$$
--   where $\|Df(z)\|$ is the operator norm of the real derivative. Then for all $z,w\in\mathbb{C}$ with $z\ne0$, $|z|<R$ and $|w|=|z|$,
--   $$\|f(z)-f(w)\|\le\pi\,\eta .$$
--
--   So the image of each circle $|z|=\rho<R$ has diameter at most $\pi\eta$. This controls the oscillation of a map on small circles around a puncture.
--
--   **Formalization Note** Differentiability and the bound are assumed pointwise on $0<\|z\|<R$; $\|Df(z)\|$ is `‖fderiv ℝ f z‖`.
-- source:
--   Elementary; used in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, proof of Theorem 9.2, pp. 154-155

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- Oscillation on circles: let `f : ℂ → E` be differentiable on the punctured disc `0 < |z| < R`
with `|z| ‖Df(z)‖ ≤ η` there. Then any two points `z, w` on a common circle `|z| = |w| < R`
around the origin satisfy `‖f z - f w‖ ≤ π η`. -/
theorem norm_sub_le_of_norm_mul_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R η : ℝ)
    (hf : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → DifferentiableAt ℝ f z ∧ ‖z‖ * ‖fderiv ℝ f z‖ ≤ η) :
    ∀ z w : ℂ, z ≠ 0 → ‖z‖ < R → ‖w‖ = ‖z‖ → ‖f z - f w‖ ≤ π * η := by
  sorry

end FiniteEnergyPlane
