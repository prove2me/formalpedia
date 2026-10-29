-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_grid_stop_limit_full_future_path_law_ws01c
-- name    : AvramDividend.Classical.bv_grid_stop_limit_full_future_path_law_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:43:37.439747+00:00
-- url     : https://prove2.me/theorems/4329f7f7-a99d-42dd-8497-4009085a2b68
-- title:
--   Finite right-approximating grid stopping clocks transfer the entire future-path Lévy law
-- statement:
--   Suppose finite observable grid clocks are stopping times and converge pointwise from above to a measurable finite raw clock. The shifted future Lévy path at that limiting clock has the same law as the original process. Every finite-dimensional marginal follows from a.s. convergence of grid increments and their stopped Lévy law; the already Proved finite-vector-to-full-path law uniqueness theorem then transfers equality to the complete product path σ-algebra. No uncountable-space weak-convergence assertion is used.
-- source:
--   Cause-linked re-publication of terminal job 636622a1-138f-4206-a6eb-c7b84657fb89, whose only reported failure was unknown import bv_grid_right_approx_future_vector_law_ws01c. The exact theorem is now canonically Proved UUID 0ed24cbc-0c8a-4d78-94bf-b7f91cda453b with accepted proof a4ca6bbd-f651-4745-9aeb-4663f731bc52. Original formal statement/preamble and 74-line source work/avram_ws01c_grid_stop_full_path_law_solution_direct.lean retained.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_all_finite_vector_laws
import Theorems.Thm_AvramDividend_Classical_bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_grid_right_approx_future_vector_law_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_grid_stop_limit_full_future_path_law_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (grid : ℕ → Ω → ℝ≥0) (raw : Ω → ℝ≥0)
    (hGridTends : ∀ ω, Tendsto (fun n => grid n ω) atTop (𝓝 (raw ω)))
    (hGridAbove : ∀ ω n, raw ω ≤ grid n ω)
    (hGridStop : ∀ n s, MeasurableSet[ℱ s] {ω : Ω | grid n ω ≤ s})
    (hRawMeas : Measurable raw) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (raw ω + t) ω - X.X (raw ω) ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by sorry
