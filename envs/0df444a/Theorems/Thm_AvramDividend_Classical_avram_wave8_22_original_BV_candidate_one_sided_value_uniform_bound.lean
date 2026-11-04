-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:09:31.082272+00:00
-- url     : https://prove2.me/theorems/00de5b03-7585-4133-a2eb-889785cb786e
-- title:
--   Original BV barrier candidate bounded on all reserves below a finite cap
-- statement:
--   The original BV value function is continuous on nonnegative reserves and zero below ruin. Thus for any finite b≥0 there is a common finite nonnegative R bounding |w(v)| for all v≤b. This includes negative overshoots and supplies the tail majorant required by the original physical negative-jump integral theorem.
-- source:
--   Canonical P3 assumptions hw_cont and hw_neg; pinned Mathlib compact continuous image bound on [0,b].

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound (w : ℝ → ℝ)
  (hwCont : ContinuousOn w (Ici 0))
  (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
  (b : ℝ) (hb : 0 ≤ b) :
  ∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → |w v| ≤ R := by sorry
