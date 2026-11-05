-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:53:04.2811+00:00
-- url     : https://prove2.me/theorems/079929e6-3baf-47c9-9225-d1bc3b1e05fc
-- title:
--   Original finite controlled stop exactly equals min(ruinTime, horizon) in extended time
-- statement:
--   For the same original spectrally negative Lévy process and controlled dividend strategy, the exact source tau=(min ruinTime n).toNNReal embeds back into ENNReal as min(ruinTime,n), since the integer horizon forces that minimum finite. Includes no-ruin, instant ruin, equality at horizon and finite ruin paths. This equality supports precise Iic/Iio horizon atom reconciliation.
-- source:
--   Original ruinTime source definition, pinned Mathlib ENNReal.coe_toNNReal and finite cast of natural horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) =
      min (ruinTime X x D ω) (n : ℝ≥0∞) := by sorry
