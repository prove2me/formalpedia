-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_dense_grid_first_downcrossing_recovers_jump_time
-- name    : AvramDividend.Classical.avram_wave7_01_path_dense_grid_first_downcrossing_recovers_jump_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:36:42.224201+00:00
-- url     : https://prove2.me/theorems/489654f6-99b3-4c0c-b1fd-636df9670aec
-- title:
--   Dense rational-grid first downcrossing identifies the exact time of any separated càdlàg downward jump
-- statement:
--   Let Y be any real path with a downward jump at time t that is separated from its surrounding path by a threshold a: all left values on (s,t) exceed a and all right values on [t,b) are below a. For a countable dense nonnegative-time grid, some start grid coordinate in (s,t) has first subsequent grid crossing below a occurring at exactly t, as an ENNReal infimum. This is pathwise correct at irrational jump times and preserves exact marks, a key part of a genuine product-measurable enumeration of source jumps.
-- source:
--   Abstract the Proved same-original-source dense grid recovery 5afb8a0d into a general path-level lemma, using DenseRange.exists_between, ENNReal.lt_iff_exists_nnreal_btwn, one-sided threshold inequalities and iInf bounds. The actual original X shifted future path is the intended consumer.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_path_dense_grid_first_downcrossing_recovers_jump_time
    (Y : ℝ≥0 → ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (s t b : ℝ≥0) (a : ℝ) (hst : s < t) (htb : t < b)
    (hL : ∀ u ∈ Ioo s t, a < Y u)
    (hR : ∀ u ∈ Ico t b, Y u < a) :
    ∃ m : ℕ, grid m ∈ Ioo s t ∧
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ | grid m < grid n ∧ Z (grid n) < a}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y) =
      (t : ℝ≥0∞) := by sorry
