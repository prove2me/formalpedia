-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_marks_negative
-- name    : AvramDividend.Classical.avram_a06_compound_driver_marks_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:23:18.896548+00:00
-- url     : https://prove2.me/theorems/a5c6fa6d-020e-481b-92d9-141dd25f0d6a
-- title:
--   All canonical compound-Poisson jump marks are strictly negative almost surely
-- statement:
--   For every mark coordinate of a genuine compound-Poisson driver with jump law uniform on (-1,0), the mark is almost surely negative. This is the exact no-positive-jumps event needed for the original sample-path spectral condition.
-- source:
--   Public Proved 4f8f174b negative mass and the IsCompoundPoissonDriver mark HasLaw provide the per-coordinate sign event.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compound_driver_marks_negative
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ n, ∀ᵐ ω ∂P, Y n ω < 0 := by sorry
