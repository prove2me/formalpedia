-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_countable_stopped_zero_occupation_variable_time_measures
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_countable_stopped_zero_occupation_variable_time_measures
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:15:10.140018+00:00
-- url     : https://prove2.me/theorems/b08153dc-2799-4b72-ba40-cb10f5a0e285
-- title:
--   Original UBV common zero-occupation event for countably many stopped clocks and varying sigma-finite time measures
-- statement:
--   For the actual original spectrally negative Levy process X, original filtration 𝓕, unbounded variation and admissible D, consider any countable family of source stopped clocks σ_n dominated pathwise by actual ruin. Give each index its own SFinite time measure μ_n, with the same dense/cofinal schedules as the Proved stopped zero-occupation result. There exists one P-almost-sure event on which, for every n, the reserve is positive μ_n-almost everywhere strictly before σ_n. No claim is made that semimartingale local time or dividend Stieltjes mass at zero vanishes, and no filtration enlargement or extra boundary regularity is introduced.
-- source:
--   Proved source stopped zero-occupation theorem 398b9dc7-99f7-4a44-aa29-e38471bd5ab1; original zero-occupation theorem 6a06830a-160f-45a6-b776-8807e202b19d; accepted common-measure countable event 7c616acd-8533-40ec-938b-7c1434b14035.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_countable_stopped_zero_occupation_variable_time_measures
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
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ n, SFinite (μ n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∀ᵐ (t : ℝ≥0) ∂μ n,
        (t : ℝ≥0∞) < σ n ω →
          0 < riskProcess X x D t ω := by sorry
