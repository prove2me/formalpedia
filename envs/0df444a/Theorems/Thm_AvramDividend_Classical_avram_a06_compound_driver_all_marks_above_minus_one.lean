-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_above_minus_one
-- name    : AvramDividend.Classical.avram_a06_compound_driver_all_marks_above_minus_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:06:19.933173+00:00
-- url     : https://prove2.me/theorems/343ffdc5-f28e-48be-b089-5849f5b48a4e
-- title:
--   All canonical compound-Poisson marks lie strictly above minus one almost surely
-- statement:
--   The uniform negative jump law on (-1,0) gives no mass to (-∞,-1]. By the exact driver mark law and countable intersection, every jump is bounded below by -1 on one full-probability event.
-- source:
--   Constructing original triplet fd251b85 and its first-moment field, alongside accepted all-marks-negative 7b3bebf3.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compound_driver_all_marks_above_minus_one
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ n, -1 < Y n ω := by sorry
