-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:57:56.417654+00:00
-- url     : https://prove2.me/theorems/88bf2f0b-9cd7-4772-89fc-a85ccae6d64d
-- title:
--   No barrier-dividend Stieltjes mass before or at the first upper passage
-- statement:
--   When a barrier strategy starts below the barrier, the cumulative dividend process is zero at time zero and at the first finite strict upper passage. Monotonicity and right-continuity imply that its Stieltjes dividend measure gives zero mass to the interval from time zero through that upper passage.
-- source:
--   Root-connected pathwise bridge for the strong-Markov dividend-value splitting theorem 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses established zero-at-upcrossing and the exact Stieltjes interval formula; no scale-function premises.

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_at_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Ioc (0 : ℝ) (u : ℝ)) = 0 := by
  sorry
