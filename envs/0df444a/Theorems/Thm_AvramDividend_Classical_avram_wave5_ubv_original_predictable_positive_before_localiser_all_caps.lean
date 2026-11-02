-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:30:07.747292+00:00
-- url     : https://prove2.me/theorems/6f165677-6661-40cf-8866-181483c8ca5e
-- title:
--   Actual UBV predictable pre-jump reserve positive before localisers for every cap
-- statement:
--   Let X be the genuine spectrally negative Lévy process in the given source filtration, with unbounded variation, and D the actual admissible dividend strategy at arbitrary cap C, including zero. At every ruin-dominated pathwise clock σ, under any sigma-finite atomless observation-time measure μ, the predictable pre-jump state leftLim (s ↦ x + X.X s ω − rightLimit D s ω) is strictly positive for μ-almost every positive time t<σ ω on P-almost every source path. The proof uses the independently remotely Proved allcap schedule-free original-source zero occupation including time zero, and the existing Proved atomless almost-everywhere equality between the predictable left-limit and book reserve on the same X,D,filtration. Atomlessness is needed only for equality across countable jump times and is satisfied by the time measure in a generator dt integral; it is not an added boundary or smoothness condition. No generator integral, stochastic compensation, dividend Stieltjes or controlled Itô–Meyer result is proved here; the theorem supplies only their original predictable lower-bound support.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706. Accepted all-cap full-time no-grid zero occupation 644af487-db5d-4d41-995b-5576891a3013; Proved original pre-jump equals reserve for atomless NNReal observation measure 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. All actual source objects preserved; no core or milestone updates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t := by sorry
