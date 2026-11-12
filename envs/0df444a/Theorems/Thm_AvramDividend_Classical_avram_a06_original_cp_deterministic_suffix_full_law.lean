-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_deterministic_suffix_full_law
-- name    : AvramDividend.Classical.avram_a06_original_cp_deterministic_suffix_full_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:18:34.00817+00:00
-- url     : https://prove2.me/theorems/3f3aca95-3da0-4019-95f4-dfe2b1141930
-- title:
--   Original exponential interarrival suffix has full infinite product law
-- statement:
--   Every deterministic suffix of the original same-probability-space marked compound-Poisson driver has the full infinite sequence law of independent unit exponential interarrivals. This is an exact iIndepFun infinitePi consequence of the driver's standing hypotheses.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_deterministic_suffix_full_law
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) :
    HasLaw (fun ω (j : ℕ) => τ (n + j) ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P := by sorry
