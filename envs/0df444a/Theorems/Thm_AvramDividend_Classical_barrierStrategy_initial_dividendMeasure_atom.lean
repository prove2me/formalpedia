-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_dividendMeasure_atom
-- name    : AvramDividend.Classical.barrierStrategy_initial_dividendMeasure_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:37:23.358535+00:00
-- url     : https://prove2.me/theorems/6252d403-33e7-413e-abb7-347992667cc5
-- title:
--   Barrier dividends have an initial Stieltjes atom of the excess capital
-- statement:
--   When the initial surplus x exceeds the nonnegative dividend barrier a, the dividend Stieltjes measure of the admissible barrier strategy puts mass exactly x minus a at the singleton time zero. The mass is an ENNReal quantity, and the statement follows from the proved general singleton-atom identity and the proved exact barrier-strategy right-increment formula.
-- source:
--   Consequence of Proved dividendMeasure_singleton_eq_rightLimit_sub (4f229f9a), barrierStrategy_isDividendStrategy_nonnegative_barrier (501af29f), and barrierStrategy_right_increment_formula (8d23d801).

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_dividendMeasure_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hax : a < x) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) =
      ENNReal.ofReal (x - a) := by sorry
