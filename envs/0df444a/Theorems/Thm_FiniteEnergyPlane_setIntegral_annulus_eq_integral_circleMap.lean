-- Prove2me | Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
-- name    : FiniteEnergyPlane.setIntegral_annulus_eq_integral_circleMap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T22:59:47.210866+00:00
-- url     : https://prove2.me/theorems/afb47e73-6b8f-4486-b0d5-0fba6e3df014
-- title:
--   Integral over an annulus in polar coordinates
-- statement:
--   Let $F$ be a real Banach space, $0<a\le b$, and $f:\mathbb{C}\to F$ continuous on the closed annulus $\{a\le|z|\le b\}$. Then
--   $$\int_{\{a\le|z|<b\}}f(z)\,dz=\int_a^b r\int_0^{2\pi}f(re^{i\theta})\,d\theta\,dr .$$
--
--   This is the polar-coordinates formula for an annulus, with $f$ only assumed continuous on the closed annulus and not on the whole disc.
--
--   **Formalization Note** The region is `ball 0 b \ ball 0 a`, and `re^{iθ}` is `circleMap 0 r θ`. The integrals are Bochner integrals; the radial integral is the interval integral `∫ r in a..b`.
-- source:
--   Standard

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Integral over an annulus in polar coordinates. Let `0 < a ≤ b` and let `f` be continuous on the
closed annulus `a ≤ |z| ≤ b`. Then
`∫_{a ≤ |z| < b} f = ∫ₐᵇ r ∫₀^{2π} f(r e^{iθ}) dθ dr`. -/
theorem setIntegral_annulus_eq_integral_circleMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (closedBall 0 b \ ball 0 a)) :
    ∫ z in ball 0 b \ ball 0 a, f z = ∫ r in a..b, r • ∫ θ in 0..2 * π, f (circleMap 0 r θ) := by
  sorry

end FiniteEnergyPlane
