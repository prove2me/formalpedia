-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_one_integrable
-- name    : AvramDividend.Classical.avram_a06_compoundPoisson_one_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:38:58.680837+00:00
-- url     : https://prove2.me/theorems/c68c66cb-c7ed-4042-8047-00aec6726152
-- title:
--   Source-exact compact-mark compound-Poisson reserve has an integrable unit-time marginal
-- statement:
--   All marks lie between −1 and 0 almost surely. Pathwise, the unit-time process lies between 1−N and 1 for a Poisson count N with finite mean, so the original process has an integrable unit-time marginal.
-- source:
--   Original-process source triplet fd251b85; public count distribution and moment, source-exact finite-sum upper/lower estimates.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_above_minus_one
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_le_drift
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_ge_drift_minus_count
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoisson_one_integrable
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    Integrable (LevyFoundations.compoundPoisson (1 : ℝ) τ Y 1) P := by sorry
