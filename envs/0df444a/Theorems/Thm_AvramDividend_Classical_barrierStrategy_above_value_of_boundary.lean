-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
-- name    : AvramDividend.Classical.barrierStrategy_above_value_of_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:42:46.9275+00:00
-- url     : https://prove2.me/theorems/fb9550bc-60e1-400d-bf18-b68dea48136b
-- title:
--   Above-barrier dividend valuation follows from the boundary value and initial lump sum
-- statement:
--   For a spectrally negative Levy process, a nonnegative cap a, and a higher initial surplus x>a, suppose the reflected-barrier strategy started at a already has its boundary value given by the nonnegative barrier-value candidate. Then the strategy started at x has the candidate's affine value. The proof composes the exact initial excess dividend payment with the generic admissible value decomposition and the proved affine formula for barrierValue.
-- source:
--   Deduction from Proved barrierStrategy_eq_add_initial_excess_above_barrier, add_initial_excess_admissible_value, barrierStrategy_admissibleLe_nonnegative_barrier and barrierValue_above_affine.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_above_value_of_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (ha : 0 ≤ a) (hax : a < x)
    (hboundary : dividendValue X q a (barrierStrategy X a a) =
      ENNReal.ofReal (barrierValue W a a))
    (hval : 0 ≤ barrierValue W a a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by sorry
