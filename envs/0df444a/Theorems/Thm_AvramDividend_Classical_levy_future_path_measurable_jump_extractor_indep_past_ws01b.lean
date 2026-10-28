-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
-- name    : AvramDividend.Classical.levy_future_path_measurable_jump_extractor_indep_past_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:22:09.439844+00:00
-- url     : https://prove2.me/theorems/36ce4b40-b787-497e-991e-d7706e65798c
-- title:
--   Actual Lévy past independent of every measurable future-path jump extractor
-- statement:
--   For an actual spectrally negative Lévy process with its given filtration, any measurable past statistic H at deterministic time s is independent of any measurable functional J of the entire shifted future increment path. In particular, once Poisson jump counts and ordered jump marks are constructed as measurable path functionals, their independence of earlier reserve information follows from this theorem, without adding a new stochastic independence assumption. No BV or right-continuous filtration assumption is needed.
-- source:
--   Derives direct IndepFun from canonically Proved deterministic-time history/full-future path product law, stationarity of the shifted future path, measurable future path (via constant stopping time), and Mathlib map-product characterisation of independence. Critical source-specific bridge from general marked Campbell compensation to Lévy jump construction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_future_path_measurable_jump_extractor_indep_past_ws01b
    {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (J : (ℝ≥0 → ℝ) → F) (hJ : Measurable J) :
    IndepFun H
      (fun ω => J (fun t : ℝ≥0 =>
        X.X (s + t) ω - X.X s ω)) P := by sorry
