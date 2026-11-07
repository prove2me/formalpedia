-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux16_finite_ennreal_real_cutoff_tendsto
-- name    : AvramDividend.Classical.avram_redux16_finite_ennreal_real_cutoff_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T11:34:18.411458+00:00
-- url     : https://prove2.me/theorems/89d14812-09e5-4b45-a9ff-837ed3bafe93
-- title:
--   Any finite nonnegative jump series converges under positive reciprocal real cutoffs
-- statement:
--   For a completely arbitrary index type and any finite extended nonnegative sum, retaining only the terms whose size exceeds the reciprocal real cutoff 1/(k+1) produces real-valued partial totals converging to the real value of the full sum. The proof relies on monotonicity, cofinality of positive reciprocal cutoffs and continuity of the ENNReal-to-real conversion under finite mass.
-- source:
--   Finite ENNReal sums; existing Proved generic real supremum theorem avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup and pinned Mathlib tendsto_atTop_iSup.

import Mathlib
open Filter Topology MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_redux16_finite_ennreal_real_cutoff_tendsto
    {α : Type*} (f : α → ℝ≥0∞) (hfinite : (∑' a : α, f a) < ⊤) :
    Tendsto (fun k : ℕ =>
      (∑' a : α,
        if ENNReal.ofReal (1 / ((k : ℝ) + 1)) < f a then f a else 0).toReal)
      atTop (𝓝 ((∑' a : α, f a).toReal)) := by sorry
