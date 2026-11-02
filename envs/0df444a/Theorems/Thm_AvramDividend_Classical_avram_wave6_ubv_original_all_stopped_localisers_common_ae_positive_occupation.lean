-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_all_stopped_localisers_common_ae_positive_occupation
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_all_stopped_localisers_common_ae_positive_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:01:45.383212+00:00
-- url     : https://prove2.me/theorems/7c616acd-8533-40ec-938b-7c1434b14035
-- title:
--   Original UBV zero-boundary occupation positivity on one common almost-sure event across all stopped clocks
-- statement:
--   For actual SpectrallyNegativeLevy P 𝓕 of unbounded variation and actual admissible D, let σ_n be any countable family of source-path random clocks individually bounded by actual ruinTime. Retain the explicit dense/cofinal schedules and sigma-finite deterministic time measure required by the accepted original stopped zero-occupation theorem. Then there is a single P-almost-sure event on which for every n, the reserve is strictly positive for μ-almost every time earlier than σ_n. Obtain it by the countable ae_all_iff intersection applied to each Proved source stopped occupation result. No new boundary smoothness, bounded variation, atomlessness, source filtration change, stochastic local time vanishing, or Stieltjes mass conclusion is claimed.
-- source:
--   Accepted original stopped source σ-finite zero occupation 398b9dc7-99f7-4a44-aa29-e38471bd5ab1; accepted source zero occupation 6a06830a-160f-45a6-b776-8807e202b19d; pinned Mathlib ae_all_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_all_stopped_localisers_common_ae_positive_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσ : ∀ n ω, σ n ω ≤ ruinTime X x D ω)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∀ᵐ (t : ℝ≥0) ∂μ,
        (t : ℝ≥0∞) < σ n ω →
          0 < riskProcess X x D t ω := by sorry
