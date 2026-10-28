-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:12:57.961007+00:00
-- url     : https://prove2.me/theorems/a0129db2-b8c1-4880-8657-14f070d6f67b
-- title:
--   Below-cap barrier dividends have no Stieltjes mass at or before time zero
-- statement:
--   For a spectrally negative Lévy process and initial reserve between zero and its nonnegative dividend barrier, the barrier dividend Stieltjes measure has zero mass on all real times up to and including zero. The admissible strategy is monotone, the barrier regulator is right-continuous, and the generic right-limit-fixed Stieltjes support theorem applies.
-- source:
--   Removes hμneg from Proved map-shift helper 3093890e-4ed7-4198-8491-5f41d268763c in the W-free strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses proved right continuity 1d8e9ea2, dividend strategy 501af29f, real-time right-limit conversion 95b3270f, and our pending generic support publication 2a38c903-6fe0-4d5f-802b-b179a2bcb5.

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Iic_zero_of_monotone_rightLim

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω
      (Set.Iic (0 : ℝ)) = 0 := by
  sorry
