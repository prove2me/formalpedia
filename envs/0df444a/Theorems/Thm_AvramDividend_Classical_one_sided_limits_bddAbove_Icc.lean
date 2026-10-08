-- Prove2me | Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
-- name    : AvramDividend.Classical.one_sided_limits_bddAbove_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T20:21:16.361533+00:00
-- url     : https://prove2.me/theorems/79c3ac43-6c33-4c4d-863a-2f4b07ffa3fc
-- title:
--   Right continuous functions with finite left limits are bounded on finite intervals
-- statement:
--   A real-valued path on nonnegative real time that is right-continuous and has a finite limit from the left at every time is bounded above on each compact interval from zero. This follows from local upper and lower boundedness obtained from the two one-sided limits, plus finite compact covering.
-- source:
--   General analytic compactness lemma to discharge the BddAbove hypothesis of the AvramDividend.Classical.barrierStrategy_reserve_cap_bound_of_bddAbove bridge; use separately with SpectrallyNegativeLevy.rightCont and leftLim.

import Mathlib

open Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.one_sided_limits_bddAbove_Icc (f : ℝ≥0 → ℝ)
    (hr : ∀ t, Tendsto f (𝓝[≥] t) (𝓝 (f t)))
    (hl : ∀ t, ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l))
    (T : ℝ≥0) :
    BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) T => f s.1)) := by
  sorry
