-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_drift_chord_ae_limit
-- name    : AvramDividend.Classical.avram_chat24_uniform_drift_chord_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:25:46.104711+00:00
-- url     : https://prove2.me/theorems/aa7ec94f-17aa-47d8-a898-78cb7c2e0e1d
-- title:
--   Almost-everywhere moving drift chord limit on a uniform mesh
-- statement:
--   Source-faithful analytic prerequisite for parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b. Apply with P(t)=v+f(t)-K(t). Summable jump losses have countable support; remove that support and zero using atomlessness. Mesh endpoints approach from the two sides. At a nonjump point, the cell mass tends to zero and P at the lower node tends to Y(t)>0. Continuous differentiability gives the moving-secant limit, with d=0 handled identically by zero numerator. Finite mesh steps vanish beyond B. No source identity, monotone K or Lipschitz premise is needed for this stronger limit result. No dependency on the parent, the native root, or the other child is introduced.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_uniform_drift_chord_ae_limit
    (f P Y : ℝ≥0 → ℝ) (d a b q : ℝ) (ha : 0 < a)
    (B : ℝ≥0) (hB : 0 < B)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto P (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (n0 : ℕ) (μ : Measure ℝ≥0) (hμ : ∀ t : ℝ≥0, μ {t} = 0) :
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
    ∀ᵐ t ∂μ, Tendsto (fun n => G n t) atTop (nhds (A t)) := by sorry
