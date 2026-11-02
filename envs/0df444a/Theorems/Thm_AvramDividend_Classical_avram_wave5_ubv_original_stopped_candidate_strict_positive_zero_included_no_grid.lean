-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_stopped_candidate_strict_positive_zero_included_no_grid
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_stopped_candidate_strict_positive_zero_included_no_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:01:30.341392+00:00
-- url     : https://prove2.me/theorems/3297bc6c-7f06-458e-a90c-b417dc547372
-- title:
--   Original UBV stopped verification candidate strictly positive at all measured times including atom at zero
-- statement:
--   For the actual native SpectrallyNegativeLevy P 𝓕 with unbounded variation and its actual capped admissible D, under the corrected w0, interior C2 and gradient assumptions, w(riskProcess X x D t ω) is strictly positive at P×μ-almost every observed time t strictly before any ruin-dominated localiser σ, including t=0 when μ has an atom there. No NullSingletonClass μ, dense grid, observation schedule, generator/extra boundary condition is added; μ merely SFinite and hxc is the corrected cap condition. Proof combines the already Proved original zero-included stopped reserve positivity with exact source alltime upper cap and inclusive closed-zero C2 secant estimate.
-- source:
--   Corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706, Proved source zero-included stopped positivity 644af487-db5d-4d41-995b-5576891a3013, alltime source cap bound and inclusive zero-endpoint C2 secant 44b01929-5817-44ac-9439-6eb3c9879f2c. No core or milestone mutation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_stopped_candidate_strict_positive_zero_included_no_grid
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
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < σ ω →
        0 < w (riskProcess X x D t ω) := by sorry
