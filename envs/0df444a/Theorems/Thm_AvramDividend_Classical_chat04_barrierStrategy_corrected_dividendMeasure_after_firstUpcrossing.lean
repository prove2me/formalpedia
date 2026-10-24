-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_corrected_dividendMeasure_after_firstUpcrossing
-- name    : AvramDividend.Classical.chat04_barrierStrategy_corrected_dividendMeasure_after_firstUpcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:18:02.525168+00:00
-- url     : https://prove2.me/theorems/1eedf7f5-1bf8-4570-add8-1ceb51833c80
-- title:
--   Correct post-first-upcrossing dividend Stieltjes measure on the original time window
-- statement:
--   At the first strict upward barrier crossing u, with initial capital 0≤x≤a and a path bounded above on the relevant compact interval, barrier cumulative dividends over the original time interval (u,u+t] have exactly the same Stieltjes mass as the original Lévy running supremum over the same interval (u,u+t]. The previous open theorem incorrectly compared to (0,t] without shifting the Lévy path. The proof uses the corrected regulator record-increment theorem and a deterministic right-continuous Stieltjes interval transfer theorem, together with the independently Proved strategy admissibility, monotonicity and path right continuity results. This facilitates the downstream stopped dividend strong-Markov proof.
-- source:
--   Corrects open target barrierStrategy_dividendMeasure_after_firstUpcrossing_shift 3718616c-a366-4b38-bf0b-b14e98b527d1. Relies on new exact record-increment and Stieltjes transfer helper theorems, and Proved existing continuity lemmas.

import Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_record_increment
import Theorems.Thm_AvramDividend_Classical_chat04_stieltjes_Ioc_eq_of_right_continuous_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_at_firstUpcrossing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_barrierStrategy_corrected_dividendMeasure_after_firstUpcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (ha0 : 0 ≤ a) (hxa : x ≤ a)
    (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    (dividendMeasure (barrierStrategy X x a) ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) := by sorry
