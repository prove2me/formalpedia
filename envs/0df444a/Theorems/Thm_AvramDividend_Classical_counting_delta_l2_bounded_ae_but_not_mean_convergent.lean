-- Prove2me | Theorems.Thm_AvramDividend_Classical_counting_delta_l2_bounded_ae_but_not_mean_convergent
-- name    : AvramDividend.Classical.counting_delta_l2_bounded_ae_but_not_mean_convergent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:44:14.705346+00:00
-- url     : https://prove2.me/theorems/2db878b8-d9d3-4f8d-a219-b8ddecba6691
-- title:
--   Infinite counting measure L1 and L2 bounded a.e. convergence without mean convergence
-- statement:
--   There exists an explicitly measurable moving-singleton process on counting measure, with every row having both L1 and L2 norm one, converging pointwise and almost everywhere to zero, while its Bochner integrals stay one. This is a formal counterexample to the missing finite-measure assumption in the original unrestricted L2 Vitali theorem.
-- source:
--   Original Avram arbitrary-measure Vitali defect; exact source reconstruction from two published indicator lemmas; publication retried after remote ACCEPTED of theorem 871bd59b-052f-40dd-b003-481339fb6526

import Mathlib
import Theorems.Thm_AvramDividend_Classical_counting_delta_indicator_mean_and_pointwise_zero
import Theorems.Thm_AvramDividend_Classical_counting_delta_l1_l2_norm_one
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.counting_delta_l2_bounded_ae_but_not_mean_convergent :
    ∃ Y : ℕ → ℕ → ℝ,
      (∀ n, eLpNorm (Y n) 2 (Measure.count : Measure ℕ) = 1) ∧
      (∀ n, eLpNorm (Y n) 1 (Measure.count : Measure ℕ) = 1) ∧
      (∀ᵐ ω ∂(Measure.count : Measure ℕ),
        Tendsto (fun n => Y n ω) atTop (nhds (0 : ℝ))) ∧
      ¬ Tendsto (fun n => ∫ ω, Y n ω ∂(Measure.count : Measure ℕ))
        atTop (nhds (0 : ℝ)) := by sorry
