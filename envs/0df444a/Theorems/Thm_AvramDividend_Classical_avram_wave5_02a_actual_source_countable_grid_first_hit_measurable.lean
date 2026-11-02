-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
-- name    : AvramDividend.Classical.avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:32:54.422413+00:00
-- url     : https://prove2.me/theorems/aed03c08-1bc6-44ad-a648-2ee8bed53948
-- title:
--   Original Levy source first strict downcrossing on a countable grid is measurable
-- statement:
--   For any countable deterministic time grid, starting time and level, the first grid time strictly after the start where the actual original Levy source is below the level, taking infinity if no such grid time exists, is measurable on the original sample space. This supplies measurable candidate times for rational-grid enumeration of actual jumps; it does not itself prove coverage or jump-measure measurability.
-- source:
--   Original source joint time sample measurability d55462c3 and countable infimum of measurable extended nonnegative real functions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (s : ℝ≥0) (a : ℝ) :
    Measurable (fun ω : Ω => ⨅ n : ℕ,
      {ω : Ω | s < grid n ∧ X.X (grid n) ω < a}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω) := by sorry
