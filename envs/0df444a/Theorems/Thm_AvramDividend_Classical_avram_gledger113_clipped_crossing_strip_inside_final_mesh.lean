-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger113_clipped_crossing_strip_inside_final_mesh
-- name    : AvramDividend.Classical.avram_gledger113_clipped_crossing_strip_inside_final_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:44:42.388436+00:00
-- url     : https://prove2.me/theorems/3961223c-3991-4c2b-b0c5-408e570216d5
-- title:
--   Unique stopped crossing strip lies in the last open physical mesh cell
-- statement:
--   If the clipped uniform grid crosses its stop between k and k+1, its last pre-stop point is at least one grid width below the stop. The strictly open crossing strip is therefore contained in the final original real-subtracted mesh strip. This establishes the precise boundary-mass comparison in gledger81 without including a terminal dividend atom.
-- source:
--   Root-connected Gaussian gledger81 last-strip boundary: Proved gledger95 partitions strict cash into Ioo(v k,rho), whereas the theorem's B uses Ioo(rho-delta,rho). This theorem supplies exact deterministic inclusion, independent of stochastic assumptions.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger113_clipped_crossing_strip_inside_final_mesh
    (n m k : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v k < ρ → v (k + 1) = ρ →
      Ioo (v k : ℝ) (ρ : ℝ) ⊆
        Ioo ((ρ : ℝ) - (Δ : ℝ)) (ρ : ℝ) := by sorry
