-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18f_finite_marked_step_sum_right_continuous
-- name    : AvramDividend.Classical.avram_ja18f_finite_marked_step_sum_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:00:37.089961+00:00
-- url     : https://prove2.me/theorems/e2cc7398-3177-4e97-9713-660734bf1ad7
-- title:
--   Every finite marked right-closed jump step sum is right-continuous at each clock
-- statement:
--   For an arbitrary finite family S of jump arrival times τ and real marks w, the time-sum over τ(i)≤s is right-continuous at every t, as a function of NNReal time. Prove each indicator step right-continuous separately: if τ≤t, it remains on for all s≥t; otherwise a neighbourhood of t stays before τ. Apply finite-sum limit. This is a sound general path regularity input for the original finite-activity marked path construction 678e826a, source finite-band sum 1c1d4731, and new child path-only theorem.
-- source:
--   Topology lemma supporting the original same-Ω physical small-band càdlàg proof, not Brownian identification.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja18f_finite_marked_step_sum_right_continuous
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => ∑ i ∈ S, if τ i ≤ s then w i else 0)
      (Ici t) t := by sorry
