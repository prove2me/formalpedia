-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_cp_original_noarrival_positive_event_raw_linear_source_exists
-- name    : AvramDividend.Classical.avram_bvb22_cp_original_noarrival_positive_event_raw_linear_source_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:18:48.072712+00:00
-- url     : https://prove2.me/theorems/6eda0aa0-0a24-4772-8bca-503dabffcb7a
-- title:
--   Original filtered unit compound-Poisson source has a strictly positive event of entirely linear no-jump sample paths through physical time one tenth
-- statement:
--   Construct the exact original product-space unit-rate compound-Poisson driver with uniformly distributed negative marks, using a Proved public source constructor. The first arrival later than one tenth has strictly positive probability by the Proved exponential survival law. On every original path in that event, the source jump count is zero simultaneously at every time through the horizon, so the raw source compound-Poisson path is precisely physical drift one times time. This supplies a complete positive-mass raw event needed for original top-cap cutoff-terminal counterexample analysis, without invoking a modified stochastic process or any false pointwise a.e. upgrade.
-- source:
--   Proved 868ae26c product driver, Proved eb667239 first-arrival survival, pinned compoundPoisson/piecewisePath/jumpCount/arrival definitions.

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_interarrival_survival
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_cp_original_noarrival_positive_event_raw_linear_source_exists :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      IsProbabilityMeasure P ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P ∧
      0 < P {ω | (1 / 10 : ℝ) < τ 0 ω} ∧
      (∀ ω, (1 / 10 : ℝ) < τ 0 ω →
        ∀ t : ℝ, t ≤ 1 / 10 →
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω = t) := by sorry
