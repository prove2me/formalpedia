-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_eq_of_positive_cumulative_and_zero_nonpositive
-- name    : AvramDividend.Classical.measure_eq_of_positive_cumulative_and_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:27:15.441144+00:00
-- url     : https://prove2.me/theorems/183b3f43-24ef-4476-871d-de954f71710f
-- title:
--   Positive cumulative interval masses determine locally finite measures with zero nonpositive mass
-- statement:
--   Two measures on real times agree whenever both have zero mass on nonpositive times and their masses on (0,t] agree for every positive t, assuming one measure is locally finite. This allows barrier-dividend cumulative Stieltjes identities to imply equality of the complete shifted measures.
-- source:
--   Mathematical bridge for strong-Markov barrier valuation 79978d61-9d1f-4b20-b8a5-114797a8e380. Use Proved cumulative Stieltjes shift 788f2fa3-ed75-4f21-9602-339f7386961a and zero pre-upcrossing measure 4396ddd6-6981-42c6-9f15-733157b72a22 to identify the future discounted reward measure.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.measure_eq_of_positive_cumulative_and_zero_nonpositive
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (hμ : μ (Set.Iic (0 : ℝ)) = 0)
    (hν : ν (Set.Iic (0 : ℝ)) = 0)
    (hcdf : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioc (0 : ℝ) t) = ν (Set.Ioc (0 : ℝ) t)) :
    μ = ν := by
  sorry
