-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a423_last_clipped_mesh_start_eventually_after_strict_early_stop
-- name    : AvramDividend.Classical.avram_ga_a423_last_clipped_mesh_start_eventually_after_strict_early_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:44:49.346671+00:00
-- url     : https://prove2.me/theorems/97ec1981-bab7-4852-9698-30dda34ed6a3
-- title:
--   Clipped terminal grid start eventually lies beyond any earlier strict stop
-- statement:
--   The last preterminal point mT/(m+1) of the refining physical grid tends to T, so every fixed stopping time ρ<T lies before the last point for all sufficiently fine grids, making the final clipped cell identically zero on that event.
-- source:
--   Proved p2_a mesh width tends to zero; original a145 terminal clipped-cell negative part integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a423_last_clipped_mesh_start_eventually_after_strict_early_stop
    (T ρ : ℝ≥0) (hρ : ρ < T) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      let Δ : ℝ≥0 := T / ((m : ℝ≥0) + 1)
      ρ ≤ (m : ℝ≥0) * Δ := by sorry
