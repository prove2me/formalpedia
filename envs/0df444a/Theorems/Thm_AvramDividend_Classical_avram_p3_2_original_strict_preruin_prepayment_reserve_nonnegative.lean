-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:52:23.713193+00:00
-- url     : https://prove2.me/theorems/b6ce799a-aae0-4bf8-9045-cff3dddaf49c
-- title:
--   Original capped admissible pre-rightpayment reserve nonnegative before ruin
-- statement:
--   For the exact original spectrally negative Lévy risk process under capped dividend admissibility, the pre-rightpayment reserve x+X_t-D_t is nonnegative at time zero and at every strictly pre-ruin time, including cap contact and with a possible positive right-horizon dividend atom.
-- source:
--   Admissibility bounds the physical post-rightpayment reserve below by zero. A proved dividendStrategy theorem bounds D_t by rightLimit D_t. The original pre-rightpayment reserve is at least the original postpayment reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_preruin_prepayment_reserve_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by sorry
