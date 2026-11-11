-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_mark_independent
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_mark_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:38:02.450195+00:00
-- url     : https://prove2.me/theorems/0ccf775e-a6d1-4c49-97bf-6307c7c52b7f
-- title:
--   Original unit-rate compound-Poisson arrival count independent of all marks
-- statement:
--   The original count of arrivals before a fixed nonnegative clock, constructed from the interarrival stream, is independent of the entire original mark sequence on the same probability space.
-- source:
--   Required hypothesis of the already Proved real random Poisson marked-sum Laplace formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_mark_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) (u : ℝ≥0) :
    IndepFun (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (u : ℝ))
      (fun ω (i : ℕ) => Y i ω) P := by sorry
