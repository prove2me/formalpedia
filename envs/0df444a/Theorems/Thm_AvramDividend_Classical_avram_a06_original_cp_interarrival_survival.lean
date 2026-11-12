-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_interarrival_survival
-- name    : AvramDividend.Classical.avram_a06_original_cp_interarrival_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:50:52.42433+00:00
-- url     : https://prove2.me/theorems/eb667239-33f5-466f-80d1-0cf3b19d7b93
-- title:
--   Original compound-Poisson interarrival waiting times obey exact unit exponential survival
-- statement:
--   For the actual rate-one compound-Poisson driver, every original waiting time has probability exp(-t) of exceeding any t≥0.
-- source:
--   Apply the Proved unit-exponential HasLaw survival identity to hd.law_interarrival n.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_interarrival_survival
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t < τ n ω} = ENNReal.ofReal (Real.exp (-t)) := by sorry
