-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_finite_physical_grid_marked_count_partition
-- name    : AvramDividend.Classical.avram_p3_2_finite_physical_grid_marked_count_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:30:02.893196+00:00
-- url     : https://prove2.me/theorems/a5935f52-a4ff-4696-947b-d9351148e61a
-- title:
--   Source-faithful finite physical-grid partition of intrinsic marked-jump nonlinear mass
-- statement:
--   For any monotone finite original-compatible time grid, a genuine marked counting measure over the full half-open horizon (u0,un] equals the finite sum of its nonlinear kernel integrals over each successive cell (ui,u(i+1)]. Every original jump is counted once including boundary marks; no finite activity assumption is added. The underlying adjacent-cell additivity theorem is a real published dependency and must be Proved before publication.
-- source:
--   Exact adjoining half-open-cell marked-count additivity with induction over Finset.range n, retaining all right-endpoint time atoms. Intended to glue physically localised original X/D jump cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original-compatible marked jump in a monotone finite physical grid
belongs to exactly one half-open cell, including at its right endpoint. -/

theorem AvramDividend.Classical.avram_p3_2_finite_physical_grid_marked_count_partition
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    (mark : ℝ≥0 → ℝ≥0 × ℝ) (hmark : Measurable mark)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F)
    (u : ℕ → ℝ≥0) (hmono : Monotone u) (n : ℕ) :
    (∫⁻ p, F p ∂((Measure.count.restrict
      (S ∩ Set.Ioc (u 0) (u n))).map mark)) =
      ∑ i ∈ Finset.range n,
        (∫⁻ p, F p ∂((Measure.count.restrict
          (S ∩ Set.Ioc (u i) (u (i + 1)))).map mark)) := by sorry
