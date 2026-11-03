-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_arbitrary_borel_path_grid_first_hit_product_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_arbitrary_borel_path_grid_first_hit_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:31:47.653198+00:00
-- url     : https://prove2.me/theorems/f38b1c92-3c84-4ffb-a122-1922eafa413b
-- title:
--   Arbitrary Borel first-grid-visit selector is measurable in the càdlàg path coordinate product sigma-algebra
-- statement:
--   For a real path indexed by nonnegative time, with the raw coordinate-product measurable structure, an arbitrary Borel state set B, an arbitrary countable time grid and a deterministic start s, the first grid time after s whose path value enters B is a measurable extended-infimum selector, mapped to nonnegative reals. This requires no invented probability space or auxiliary process and supplies the generic product-measurable first-crossing ingredient for enumerating exact jumps of the original Lévy shifted future path.
-- source:
--   Adapt the Proved original-process first strict grid downcrossing measurable argument aed03c08 to arbitrary Borel state membership using measurable_pi_apply and countable Measurable.iInf; ENNReal.measurable_toNNReal completes the selector.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_arbitrary_borel_path_grid_first_hit_product_measurable
    (B : Set ℝ) (hB : MeasurableSet B)
    (grid : ℕ → ℝ≥0) (s : ℝ≥0) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      (⨅ n : ℕ,
        {Y : ℝ≥0 → ℝ | s < grid n ∧ Y (grid n) ∈ B}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal) := by sorry
