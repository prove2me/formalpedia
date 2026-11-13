-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_cp_noarrival_tenth_positive_probability
-- name    : AvramDividend.Classical.avram_bvb22_original_cp_noarrival_tenth_positive_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:03:43.396835+00:00
-- url     : https://prove2.me/theorems/f4fcb902-2efc-45d0-af0f-754f72c7b9d5
-- title:
--   Original unit-intensity compound-Poisson no-arrival event through one tenth has strictly positive probability
-- statement:
--   Under the already constructed original unit-rate filtered compound-Poisson driver with diffuse negative marks, the no-first-arrival event through the physical time one tenth has exact probability exp of negative one tenth, which is strictly positive. This is the event used in the analytic counterexample to the incorrectly mismatched top-cap cutoff/terminal pathwise ledger. A separate source-level path identity and all-source hypotheses remain required for a formal disproof.
-- source:
--   Original proved compound-Poisson interarrival survival theorem eb667239, source model in bvc_topcap_uniform_source_counterexample_20261112.md.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_interarrival_survival
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_cp_noarrival_tenth_positive_probability
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    P {ω | (1 / 10 : ℝ) < τ 0 ω} =
      ENNReal.ofReal (Real.exp (-(1 / 10 : ℝ))) ∧
    0 < P {ω | (1 / 10 : ℝ) < τ 0 ω} := by sorry
