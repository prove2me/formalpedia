-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_sq_lintegral_mul_le
-- name    : DbarRegularity.lintegral_sq_lintegral_mul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:58:45.45255+00:00
-- url     : https://prove2.me/theorems/4cf28963-8044-4efa-9283-93bbd371add6
-- title:
--   Young's inequality $\||h|*|f|\|_2\le\|h\|_2\|f\|_1$ on $\mathbb R^d$ (squared lower-integral form)
-- statement:
--   Let $d\ge0$ and let $h,f:\mathbb R^d\to\mathbb C$ be almost-everywhere strongly measurable. Then
--   $$\int_{\mathbb R^d}\Big(\int_{\mathbb R^d}|h(x-y)|\,|f(y)|\,dy\Big)^2dx\;\le\;\Big(\int_{\mathbb R^d}|h|^2\Big)\Big(\int_{\mathbb R^d}|f|\Big)^2 .$$
--   In other words $\big\||h|*|f|\big\|_{L^2}\le\|h\|_{L^2}\|f\|_{L^1}$, the $L^2\times L^1\to L^2$ case of Young's convolution inequality, stated for absolute values and without any finiteness assumptions.
--
--   Besides the norm bound for convolutions, it shows that when $h\in L^2$ and $f\in L^1$ the integral $\int|h(x-y)||f(y)|\,dy$ is finite for almost every $x$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. All integrals are lower Lebesgue integrals `∫⁻` of extended nonnegative reals, absolute values are `‖·‖ₑ`, and squares are natural-number powers in `ℝ≥0∞`. Only `AEStronglyMeasurable` is assumed; both sides may be infinite.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For measurable `h, f : ℝ^d → ℂ`,
`∫ (∫ |h(x - y)| |f(y)| dy)² dx ≤ (∫ |h|²) (∫ |f|)²`. -/
theorem lintegral_sq_lintegral_mul_le {d : ℕ} (h f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2
      ≤ (∫⁻ x, ‖h x‖ₑ ^ 2) * (∫⁻ y, ‖f y‖ₑ) ^ 2 := by sorry

end DbarRegularity
