-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_finite_stopping_candidate_strict_positive_before_ruin
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_finite_stopping_candidate_strict_positive_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:35:33.830196+00:00
-- url     : https://prove2.me/theorems/e70e6065-1bfc-4074-90d4-14c90f3f2da8
-- title:
--   Corrected UBV candidate strictly positive at every finite original-filtration stopped pre-ruin endpoint
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕 of unbounded variation, any actual admissible strategy D at arbitrary cap C, and any finite right-continuous-original-filtration stopping clock τ satisfying exactly the source stopping hypotheses, w of the original controlled reserve at τ is strictly positive P-almost surely on τ<ruinTime. This uses the Proved source finite-stopping strict reserve positivity, all-cap original reserve bound, and inclusive-cap derivative secant with 0≤w0. It imposes no smoothness at zero, no positive cap, no-creeping, atomless-time measure, or extra filtration restriction. At the equality τ=ruinTime only nonnegativity is asserted by separate terminal theorem. This is a boundary endpoint value sign proof, not integration or martingale compensation.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; reuse Proved original finite-stopping strict reserve 9cc18bac-2e55-4eec-afe8-0888ccecff75, capped reserve alltimes, and inclusive allcap secant 44b01929-5817-44ac-9439-6eb3c9879f2c. No target submission or milestone change.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_finite_stopping_candidate_strict_positive_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      0 < w (riskProcess X x D (τ ω) ω) := by sorry
