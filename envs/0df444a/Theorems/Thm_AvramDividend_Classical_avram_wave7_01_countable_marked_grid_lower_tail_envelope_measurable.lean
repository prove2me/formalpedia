-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:42:28.38469+00:00
-- url     : https://prove2.me/theorems/dcb3d585-d64e-4330-aec0-7bcf7629ee88
-- title:
--   Lower tail envelope of finite Borel marked-increment grid counts is path-product measurable
-- statement:
--   For any Borel mark set and any countable family of finite real-valued coordinate increment grids, the ENNReal lower tail envelope sup_m inf_{k≥m} count_k is measurable in the coordinate product σ-algebra of all paths. This provides a robust liminf-type candidate for intrinsic càdlàg jump-count approximation, avoiding the spurious coarse-grid maxima introduced by unrestricted suprema. No equality with the true jump measure is asserted.
-- source:
--   Each finite marked-grid count is a finite sum of measurable Borel-set indicator functions and hence measurable; coerce counts to ENNReal, take conditional pointwise count/⊤ and use countable measurable_iInf and measurable_iSup.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ⨆ m : ℕ, ⨅ k : ℕ, if m ≤ k then ((((Finset.range (n k)).filter (fun i =>
          Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)) else ⊤) := by sorry
