-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_candidate_strict_positive_before_localiser
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_predictable_candidate_strict_positive_before_localiser
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:26:26.735993+00:00
-- url     : https://prove2.me/theorems/01d0d28c-106a-4e9d-bef5-7418e4279899
-- title:
--   Original UBV predictable verification value is strictly positive before every genuine pre-ruin localiser at all caps
-- statement:
--   For an actual SpectrallyNegativeLevy P 𝓕 of unbounded variation and actual admissible strategy D, the verification function w at the predictable left-limit reserve is strictly positive at μ-almost every positive time strictly before any original pre-ruin localiser σ≤ruinTime. The atomless σ-finite-time observation measure is required by the existing source equalities and zero occupation; no new boundary, filtration, regularity, cap positivity, or finite-cap assumptions. Uses Proved all-cap predictable left-reserve positivity (including zero-occupation), original atomless left-limit/book-reserve equality, actual cap constraint, and the Proved inclusive gradient secant with 0≤w0 to derive w(y)>0 for y>0. No Ito-Meyer or dividend Stieltjes integration.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; Proved predictable positivity 6f165677-6661-40cf-8866-181483c8ca5e, Proved original atomless equality 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d, and inclusive allcap secant 44b01929-5817-44ac-9439-6eb3c9879f2c. No change to core or milestones.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_predictable_candidate_strict_positive_before_localiser
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
        0 < w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by sorry
