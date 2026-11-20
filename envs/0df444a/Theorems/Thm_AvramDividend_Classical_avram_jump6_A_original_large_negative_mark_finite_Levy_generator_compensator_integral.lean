-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
-- name    : AvramDividend.Classical.avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:02:24.347506+00:00
-- url     : https://prove2.me/theorems/686e3545-2282-4a79-9eb8-918431263cd0
-- title:
--   Exact finite-activity original nonlinear large-negative-jump compensator integral
-- statement:
--   For a genuine spectrally negative Lévy process with finite negative jump intensity supported on marks z≤−2, the true nonlinear generator integrand of the original piecewise quadratic HJB value w at reserve 0≤y≤1/5 is −(1+y+y²) ν-a.e. Hence the genuine marked generator compensator integral over negative marks equals −(1+y+y²)×ν((-∞,0)). This extends the physically exact negative-two Dirac case to all finite-activity large-negative Lévy laws and replaces the invalid raw unit-fullmark compensation in the original stopped Itô verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z ∂X.ν) =
    -(1 + y + y ^ 2) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
