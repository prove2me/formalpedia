-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_brownian_stationary_positive_increments
-- name    : AvramDividend.Classical.avram_wave3_04_drifted_brownian_stationary_positive_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:30:50.853208+00:00
-- url     : https://prove2.me/theorems/646ddfc2-0c92-4a4b-9f39-96562dafb474
-- title:
--   Negative-drift Brownian increments are stationary under the genuine Gaussian law
-- statement:
--   The increment of Brownian motion with deterministic drift minus one between two strictly ordered nonnegative times has the same probability distribution as the drifted process over their elapsed time. This builds the positive-duration stationary-increment field needed to construct a concrete Gaussian SpectrallyNegativeLevy witness for the UBV verification counterexample, using the actual original Brownian law and no axiom of stationary increments.
-- source:
--   Previously Proved exact Brownian Gaussian increment law 2e1a61eb-85bd-4d58-8a98-831b295e2059 and drifted marginal law 71cbe501-8abc-41d4-b1c9-50d9151f3025, pinned Mathlib IdentDistrib. Remote private full source passed sentinel job c2bcfb70-bde5-412a-b7e5-87bbc28fa298 SHA 8f5eef192f634c079fc541f573360303c3df44e782393bd12aef9b3e9ea989f3.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_increment_gaussian
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_gaussian_law

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem AvramDividend.Classical.avram_wave3_04_drifted_brownian_stationary_positive_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s t : ℝ≥0) (hst : s < t) :
    IdentDistrib
      (fun ω => (W.W (t : ℝ) ω - W.W (s : ℝ) ω) -
        ((t : ℝ) - (s : ℝ)))
      (fun ω => W.W ((t - s : ℝ≥0) : ℝ) ω -
        ((t - s : ℝ≥0) : ℝ)) P P := by sorry
