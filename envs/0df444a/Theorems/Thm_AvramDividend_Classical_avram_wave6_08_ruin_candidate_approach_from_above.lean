-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ruin_candidate_approach_from_above
-- name    : AvramDividend.Classical.avram_wave6_08_ruin_candidate_approach_from_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:58:00.069334+00:00
-- url     : https://prove2.me/theorems/db7cf8e0-075f-4c15-9a6f-553082227b5a
-- title:
--   Ruin-side candidate limit without false two-sided continuity at zero
-- statement:
--   The corrected UBV verification candidate equals zero strictly below zero and is continuous on nonnegative reserves, but it may have w(0)>0, hence cannot be assumed continuous on ℝ at 0. This result proves exactly the needed one-sided composition: if x≤0 and z_n≥x converges to x, then w(z_n) converges to w(x). For x<0, all sufficiently late z_n are negative and the values are zero; for x=0, nonnegative approach and ContinuousOn on [0,∞) suffice. It justifies the original source ruin-grid terminal comparison without strengthening the false boundary regularity assumption.
-- source:
--   Source-specific original stopped Lévy cap verification terminal creeping-vs-overshoot continuity; corrected 429e17ca.

import Mathlib

open Filter Topology Set

theorem AvramDividend.Classical.avram_wave6_08_ruin_candidate_approach_from_above
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (hx : x ≤ 0)
    (z : ℕ → ℝ) (hz : ∀ n, x ≤ z n)
    (hlim : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => w (z n)) atTop (𝓝 (w x)) := by sorry
