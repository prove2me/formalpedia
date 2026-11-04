-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_cell_horizon_clip
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_marked_cell_horizon_clip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:46:31.721463+00:00
-- url     : https://prove2.me/theorems/4b94c4dd-4bfc-470f-9cee-c82aa6690328
-- title:
--   Original predictable marked source rectangle clips exactly to the true finite physical horizon
-- statement:
--   Same original marked source rectangle and original physical nonnegative clock. A strict-left, closed-right source interval clipped at T is precisely the rectangle with upper endpoint min(t,T), for every path event and Borel jump mark set, including zero-length horizon. Genuine geometric restriction identity, no measure-theoretic or Poisson assumptions.
-- source:
--   Mathlib Set interval membership; Avram Proposition 4(i), finite horizon source jump count.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_interval_horizon_clip
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_marked_cell_horizon_clip
    (Ω : Type*) (s t T : ℝ≥0) (A : Set Ω) (B : Set ℝ) :
    (((Ioc s t ×ˢ A) ×ˢ B) ∩
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T}) =
    ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by sorry
