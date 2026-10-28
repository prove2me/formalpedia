-- Prove2me | Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
-- name    : FiniteEnergyPlane.integral_mul_integral_bilin_circleMap_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T22:59:47.792713+00:00
-- url     : https://prove2.me/theorems/e013bcfa-fd75-4678-8a95-adf96e223ce1
-- title:
--   Annulus identity for a constant 2-form in polar coordinates
-- statement:
--   Let $F$ be a real Banach space, $\sigma:F\times F\to\mathbb{R}$ a continuous bilinear form with $\sigma(x,y)=-\sigma(y,x)$, and $q\in F$. Let $0<a\le b$ and let $u$ be of class $C^2$ on an open set $U\subseteq\mathbb{C}$ containing the closed annulus $\{a\le|z|\le b\}$. Writing $z=re^{i\theta}$ and $\partial_\theta u(re^{i\theta})=Du(re^{i\theta})(ire^{i\theta})$,
--   $$\int_a^b r\int_0^{2\pi}\sigma\big(\partial_s u,\partial_t u\big)(re^{i\theta})\,d\theta\,dr=\frac12\int_0^{2\pi}\sigma\big(u(be^{i\theta})-q,\ \partial_\theta u(be^{i\theta})\big)\,d\theta-\frac12\int_0^{2\pi}\sigma\big(u(ae^{i\theta})-q,\ \partial_\theta u(ae^{i\theta})\big)\,d\theta ,$$
--   where $\partial_s u=Du(\cdot)\,1$ and $\partial_t u=Du(\cdot)\,i$.
--
--   This expresses the integral of the pullback of a constant 2-form over an annulus by boundary terms on its two circles. It is the identity behind energy estimates for pseudoholomorphic maps near a puncture.
--
--   **Formalization Note** The circles are parametrized by `circleMap 0 r θ` for `θ ∈ [0, 2π]`, and `∂_θ u` is `fderiv ℝ u (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)`. The annulus integral is written in polar coordinates as an iterated interval integral, with the Jacobian factor `r`.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Section 4

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Annulus identity for a constant 2-form. Let `σ` be an antisymmetric continuous bilinear form
on `F`, `q ∈ F`, `0 < a ≤ b`, and let `u` be of class `C²` on an open set containing the closed
annulus `a ≤ |z| ≤ b`. Then the integral over the annulus, in polar coordinates, of
`σ(∂ₛu, ∂ₜu)` equals `½ ∫ σ(u - q, ∂_θ u) dθ` on the circle of radius `b` minus the same term on the
circle of radius `a`. Here `∂_θ u (r e^{iθ}) = Du(r e^{iθ}) (i r e^{iθ})`. -/
theorem integral_mul_integral_bilin_circleMap_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (σ : F →L[ℝ] F →L[ℝ] ℝ) (hσ : ∀ x y, σ x y = -σ y x)
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F} (hu : ContDiffOn ℝ 2 u U) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) (q : F) :
    ∫ r in a..b, r * ∫ θ in 0..2 * π,
        σ (fderiv ℝ u (circleMap 0 r θ) 1) (fderiv ℝ u (circleMap 0 r θ) Complex.I) =
      (1 / 2) * (∫ θ in 0..2 * π, σ (u (circleMap 0 b θ) - q)
          (fderiv ℝ u (circleMap 0 b θ) (circleMap 0 b θ * Complex.I))) -
        (1 / 2) * (∫ θ in 0..2 * π, σ (u (circleMap 0 a θ) - q)
          (fderiv ℝ u (circleMap 0 a θ) (circleMap 0 a θ * Complex.I))) := by
  sorry

end FiniteEnergyPlane
