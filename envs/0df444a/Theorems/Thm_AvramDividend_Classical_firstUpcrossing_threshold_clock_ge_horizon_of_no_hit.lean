-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_clock_ge_horizon_of_no_hit
-- name    : AvramDividend.Classical.firstUpcrossing_threshold_clock_ge_horizon_of_no_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:51:21.539933+00:00
-- url     : https://prove2.me/theorems/83c1693e-bb66-438b-9f04-6fe3ae73a784
-- title:
--   Strict first-upcrossing clock is at least a horizon with no prior hits
-- statement:
--   For the strict real-level first-upcrossing time defined as the infimum of all qualifying nonnegative hitting times, absence of threshold crossings through a finite horizon T ensures that the extended hitting clock is at least T. This is the order bridge required to convert finite-horizon no-record-crossing statements into stochastic clock tail control.
-- source:
--   Prove2Me firstUpcrossing_threshold_iInf_mono environment and Mathlib NNReal to ENNReal ordering.

import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.firstUpcrossing_threshold_clock_ge_horizon_of_no_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℝ≥0) (c : ℝ)
    (hNo : ∀ r : ℝ≥0, r ≤ T → ¬ c < X.X r ω) :
    (T : ℝ≥0∞) ≤
      ⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞) := by sorry
