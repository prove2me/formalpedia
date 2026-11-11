-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_exp_ae_upper_bound
-- name    : AvramDividend.Classical.avram_a06_compoundPoisson_exp_ae_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:02:12.693585+00:00
-- url     : https://prove2.me/theorems/11292bf6-72b5-4dc3-9715-aa6b0f54733a
-- title:
--   Canonical negative-mark compound-Poisson exponential upper bound almost everywhere
-- statement:
--   On one full-probability event for all negative marks, all nonnegative Laplace frequencies and times have exponential reward bounded by the exponential of physical drift. Reuses proven pathwise bound and the common mark-sign event.
-- source:
--   Public root-connected source constructor fd251b85; deterministic bound ec1d7668 and common negative-mark event 7b3bebf3.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_le_drift
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoisson_exp_ae_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ t θ : ℝ, 0 ≤ θ →
      Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω) ≤
        Real.exp (θ * t) := by sorry
