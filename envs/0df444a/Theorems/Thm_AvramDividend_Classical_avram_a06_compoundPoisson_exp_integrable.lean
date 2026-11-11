-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_exp_integrable
-- name    : AvramDividend.Classical.avram_a06_compoundPoisson_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:04:20.325436+00:00
-- url     : https://prove2.me/theorems/3a5966f6-81bd-4ebf-839f-f41843d28130
-- title:
--   Canonical compound-Poisson nonnegative Laplace exponential is integrable
-- statement:
--   The fixed-time canonical compound-Poisson path is measurable, and its positive exponential is bounded almost everywhere by the deterministic drift exponential, hence integrable under the probability law.
-- source:
--   Root-connected source triplet fd251b85, using published public fixed-time measurability b3ae2168, all negative marks 7b3bebf3 and path upper bound ec1d7668.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_le_drift
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoisson_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω)) P := by sorry
