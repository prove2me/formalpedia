-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
-- name    : AvramDividend.Classical.avram_a06_compound_driver_all_marks_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:43:43.355238+00:00
-- url     : https://prove2.me/theorems/7b3bebf3-0716-458d-bf13-932dd3002c0b
-- title:
--   Simultaneous almost-sure negativity of every original compound-Poisson mark
-- statement:
--   On one common probability-one event every jump mark in the original compound-Poisson driver is strictly negative. Needed to gate all sample paths and establish no positive jumps.
-- source:
--   Public Proved avram_a06_compound_driver_marks_negative and Mathlib MeasureTheory.ae_all_iff on the countable index ℕ.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_marks_negative
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compound_driver_all_marks_negative
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω < 0 := by sorry
