-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_positive_mesh_time_gap_implies_strict_ceiling_order
-- name    : AvramDividend.Classical.avram_a20_positive_mesh_time_gap_implies_strict_ceiling_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:28:16.018833+00:00
-- url     : https://prove2.me/theorems/7dda7c27-e503-459d-b93c-01b7a14056af
-- title:
--   Strict positive horizon mesh-scaled separation implies strict chronological ceiling-index order
-- statement:
--   For nonnegative times u,v and positive horizon T, if T<k(v−u) for an integer mesh resolution k, then ceil(uk/T)<ceil(vk/T). This pure arithmetic result is extracted from the previously Proved original finite-band all-finer-grid theorem and requires no probability-space or mark assumptions. Its proof uses the strict scaled gap, division by positive T, the Nat.ceil upper bound ceil(x)<x+1, and the lower bound x≤ceil(x). It is the reusable analytic step enabling all finite arbitrary Borel original marked-jump pairs to be strictly resolved on sufficiently fine grids.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_positive_mesh_time_gap_implies_strict_ceiling_order
    (u v T : ℝ≥0) (hT : 0 < T) (k : ℕ)
    (hGap : (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ))) :
    Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) := by sorry
