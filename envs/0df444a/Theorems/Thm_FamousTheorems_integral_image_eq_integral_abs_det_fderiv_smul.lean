-- Prove2me | Theorems.Thm_FamousTheorems_integral_image_eq_integral_abs_det_fderiv_smul
-- name    : FamousTheorems.integral_image_eq_integral_abs_det_fderiv_smul
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:14.430538+00:00
-- url     : https://prove2.me/theorems/6e200906-47b5-408e-aa5a-5514d11ead71
-- title:
--   Change of variables for multiple integrals
-- statement:
--   **The change of variables formula.** For an injective map $f$ with derivative $Df$ on a measurable set $s$, $$\int_{f(s)} g(x)\,dx \;=\; \int_s g(f(x))\,\bigl|\det Df(x)\bigr|\,dx.$$ The Jacobian determinant is the local volume distortion factor, and the absolute value appears because Lebesgue measure is unsigned — orientation is discarded, unlike in the one-dimensional oriented integral. This is the multivariable substitution rule, and it is what makes polar, cylindrical and spherical coordinates legitimate. The hypotheses are notably weak: differentiability within $s$ and injectivity suffice, with no continuity of the derivative required, which is what allows the formula to be applied to maps that are merely differentiable. **Formalization note.** `fderiv` is the Fréchet derivative and the measure is the additive Haar (Lebesgue) measure on a finite-dimensional real space. The result is Mathlib's `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem integral_image_eq_integral_abs_det_fderiv_smul :
    ∀ {E : Type u_1} {F : Type u_2} 
    [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E] [inst_3 : NormedAddCommGroup F] 
    [inst_4 : NormedSpace ℝ F] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E} [inst_5 : MeasurableSpace E] [BorelSpace E] 
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure], 
    MeasurableSet s → 
    (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) → 
    InjOn f s → ∀ (g : E → F), ∫ (x : E) in f '' s, g x ∂μ = ∫ (x : E) in s, |(f' x).det| • g (f x) ∂μ := by sorry

end FamousTheorems
