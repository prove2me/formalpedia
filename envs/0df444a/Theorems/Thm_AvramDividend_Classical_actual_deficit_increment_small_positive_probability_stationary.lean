-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_deficit_increment_small_positive_probability_stationary
-- name    : AvramDividend.Classical.actual_deficit_increment_small_positive_probability_stationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:37:25.634978+00:00
-- url     : https://prove2.me/theorems/8d9e7a79-1127-4c00-b40b-fae8ad89851b
-- title:
--   Small positive drift-deficit increment event has the fixed-duration stationary probability
-- statement:
--   The probability that the actual compensated drift deficit increases by a positive amount at most b on an interval [s,t] equals the probability that its one-time deficit at length t-s falls in (0,b]. This precise real-measure event equality comes from the accepted stationary IdentDistrib law applied to the Borel interval (0,b]. It is the probability transfer needed to bound each grid cell by the same Laplace-derived small-positive-deficit probability.
-- source:
--   Canonical Lévy stationary increment law and Mathlib IdentDistrib.measure_mem_eq; Avram, Palmowski and Pistorius (2007), §3.3.

import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.actual_deficit_increment_small_positive_probability_stationary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (b : ℝ) :
    P.real {ω : Ω |
      0 < (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) ∧
      (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) ≤ b} =
    P.real {ω : Ω |
      0 < X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t - s) ω ∧
      X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t - s) ω ≤ b} := by sorry
