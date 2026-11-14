-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_drift_chord_pointwise_no_jump
-- name    : AvramDividend.Classical.avram_chat24_uniform_drift_chord_pointwise_no_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:19:59.290444+00:00
-- url     : https://prove2.me/theorems/a2bf4695-628f-49e6-ac17-bf0b48efe4f2
-- title:
--   Uniform drift chords converge pointwise away from jump support
-- statement:
--   Exact pointwise prerequisite of parent aa7ec94f-17aa-47d8-a898-78cb7c2e0e1d. Remove the summability and atomless-measure assumptions and replace the almost-everywhere conclusion by convergence at one fixed positive t whose truncated jump is zero. On 0<t≤B, shrinking strict-left cells give P(lower)→Y(t), f(upper)-f(lower)→f(t)-leftLim f(t)=0, so the cell mass tends to zero. C1 smoothness yields the moving chord derivative limit and the discount converges by continuity. For t>B every cell indicator and the target vanish. The parent discards the singleton {0} separately using atomlessness: its A(0) need not vanish. The parent follows because the summable truncated-jump function has countable support and the measure gives every singleton zero mass. No dependency on the parent is present; no summability or measure hypothesis is hidden in the pointwise claim.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_uniform_drift_chord_pointwise_no_jump
    (f P Y : ℝ≥0 → ℝ) (d a b q : ℝ) (ha : 0 < a)
    (B : ℝ≥0) (hB : 0 < B)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto P (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (n0 : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (hzero : (if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0) = 0) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (P (u n i) + d * h n - m n i) - w (P (u n i) - m n i)) / h n)
        else 0
      else 0
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0
    Tendsto (fun n => G n t) atTop (nhds (A t)) := by sorry
