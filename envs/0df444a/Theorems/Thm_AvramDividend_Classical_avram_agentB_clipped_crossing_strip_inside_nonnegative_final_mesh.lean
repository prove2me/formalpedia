-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_clipped_crossing_strip_inside_nonnegative_final_mesh
-- name    : AvramDividend.Classical.avram_agentB_clipped_crossing_strip_inside_nonnegative_final_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T00:00:59.523879+00:00
-- url     : https://prove2.me/theorems/b49c6942-bdce-4a21-a9ba-ed5fb2eeecc7
-- title:
--   True stopped crossing strip lies inside final mesh with NNReal-clamped lower endpoint
-- statement:
--   For the original uniform clipped grid up to the positive stopping clock rho, if k is the first crossing index, the open strip (v_k,rho) lies inside (rho - Delta,rho) with the subtraction taken in NNReal, hence clamped at zero. This strengthens Proved gledger113 and prevents the spurious inclusion of the dividend atom at time zero when rho is shorter than one mesh width.
-- source:
--   Proved avram_gledger113_clipped_crossing_strip_inside_final_mesh; use its proven rho <= v_k+Delta argument and ordered NNReal truncated subtraction tsub_le_iff_right, then coerce the inequality to real.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_clipped_crossing_strip_inside_nonnegative_final_mesh
    (n m k : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v k < ρ → v (k + 1) = ρ →
      Ioo (v k : ℝ) (ρ : ℝ) ⊆
        Ioo ((ρ - Δ : ℝ≥0) : ℝ) (ρ : ℝ) := by sorry
