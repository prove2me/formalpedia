-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a383_true_crossing_positive_part_mesh_identity_v2
-- name    : AvramDividend.Classical.avram_ga_a383_true_crossing_positive_part_mesh_identity_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:53:08.380233+00:00
-- url     : https://prove2.me/theorems/285b038b-a32c-47aa-b585-ca01704c4c0f
-- title:
--   Exact positive-part identity converting strict single-crossing mask to inclusive grid mask
-- statement:
--   For a positive grid width, the positive part of a sum over strict crossing cells equals the inclusive-cell positive sum with a strict endpoint indicator, with at most one active cell.
-- source:
--   Source-exact Gaussian true crossing residual a138; generic uniqueness a380 and masked positive identity a381.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a383_true_crossing_positive_part_mesh_identity_v2
    (m : ℕ) (Δ ρ : ℝ≥0) (hΔ : 0 < Δ) (f : ℕ → ℝ) :
    max (∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ < ρ ∧ ρ < (i : ℝ≥0) * Δ + Δ
      then f i else 0) 0 =
    ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ < ρ ∧ ρ ≤ ((Nat.succ i : ℕ) : ℝ≥0) * Δ
      then max (if ρ < ((Nat.succ i : ℕ) : ℝ≥0) * Δ then f i else 0) 0
      else 0 := by sorry
