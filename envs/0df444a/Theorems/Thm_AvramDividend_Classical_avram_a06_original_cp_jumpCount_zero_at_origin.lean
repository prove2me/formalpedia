-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_jumpCount_zero_at_origin
-- name    : AvramDividend.Classical.avram_a06_original_cp_jumpCount_zero_at_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:45:45.349796+00:00
-- url     : https://prove2.me/theorems/01d6595f-bc10-4b64-ad36-cd446a923d39
-- title:
--   Original compound-Poisson arrival count vanishes almost surely at time zero
-- statement:
--   Because the original compound-Poisson first interarrival is strictly positive almost surely, its arrival-count path at time zero is zero almost surely.
-- source:
--   Use accepted levy_foundations_compoundDriverInterarrivalPositive and levy_foundations_jumpCountZeroBeforeFirst; simp the original arrival at index zero to the first interarrival.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_jumpCount_zero_at_origin
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ) = 0 := by sorry
