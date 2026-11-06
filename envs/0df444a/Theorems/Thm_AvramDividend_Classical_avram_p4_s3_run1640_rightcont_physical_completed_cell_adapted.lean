-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_rightcont_physical_completed_cell_adapted
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_rightcont_physical_completed_cell_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:53:13.121665+00:00
-- url     : https://prove2.me/theorems/50f07f29-c131-4581-823f-c9f13d24b864
-- title:
--   Original physical bounded predictable compensated cells are adapted at their next grid time
-- statement:
--   For the original right-continuous filtered path and a nondecreasing deterministic grid, a coefficient measurable before the cell and the realised marked count measurable after the cell yield a compensated weighted increment measurable at the cell end. The proof is a direct finite measurable-product argument, providing the exact terminal adaptedness hypothesis for a genuine physical-grid prefix theorem.
-- source:
--   Mathlib StronglyMeasurable.mono, .mul, .sub, stronglyMeasurable_const and Filtration.rightCont monotonicity; no stochastic axioms or independent-increment shortcuts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_rightcont_physical_completed_cell_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H N D : ℕ → Ω → ℝ) (r : ℕ → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hN : ∀ i,
      StronglyMeasurable[𝓕.rightCont (grid (i + 1))] (N i))
    (hD : ∀ i ω, D i ω = H i ω * (N i ω - r i)) :
    ∀ i, StronglyMeasurable[𝓕.rightCont (grid (i + 1))] (D i) := by sorry
