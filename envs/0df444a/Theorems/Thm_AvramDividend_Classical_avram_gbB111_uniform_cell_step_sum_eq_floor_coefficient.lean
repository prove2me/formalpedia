-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
-- name    : AvramDividend.Classical.avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:50:28.918883+00:00
-- url     : https://prove2.me/theorems/359c724a-d13f-431e-a6ab-4c5094c75fe4
-- title:
--   Original finite uniform step sum equals its floor-selected coefficient
-- statement:
--   For the exact original m+1 uniform cells over [0,T), the finite sum of mutually exclusive half-open cell indicators with arbitrary coefficient weights c equals the coefficient at index Nat.floor(t/(T/(m+1))). It follows from the already Proved BVA20 original floor-step identity by rescaling its horizon from T to T*(m+2)/(m+1). This directly supplies the B102 step-to-floor-index representation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
    (T : ℝ) (hT : 0 < T) (m : ℕ)
    (c : ℕ → ℝ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    let Δ : ℝ := T / ((m : ℝ) + 1)
    (Finset.range (m + 1)).sum (fun i =>
      if ((i : ℝ) * Δ ≤ t ∧
        t < (((i + 1 : ℕ) : ℝ) * Δ)) then c i else 0) =
    c ⌊t / Δ⌋₊ := by sorry
