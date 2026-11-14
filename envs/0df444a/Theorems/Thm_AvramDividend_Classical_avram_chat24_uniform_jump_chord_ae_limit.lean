-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_jump_chord_ae_limit
-- name    : AvramDividend.Classical.avram_chat24_uniform_jump_chord_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:56:45.261274+00:00
-- url     : https://prove2.me/theorems/7148e5e3-d521-4a02-9b16-15f9f757c1a9
-- title:
--   Uniform cell jump chords converge at the mapped atoms
-- statement:
--   The exact last conjunct of parent eff78840-bf10-4dc9-a987-78b8e980b923. At a positive nonzero downward jump select the unique strict-left cell. Right continuity and the left limits imply V tends to Y(t), m tends to leftLim f(t)-f(t)>0, and the upper endpoint tends to t. Monotone K and the band hypothesis prove V-m>=a-d*h, so the limiting lower payoff argument Y(t)+delta is >=a>0. Smoothness gives continuity at both limiting payoff arguments. The quotient times the negative mark tends to the jump difference. Outside B all mesh indicators vanish. Transfer these pointwise facts through the measurable jump graph to the mapped count measure. Retain hK and hband to justify the positive limiting domain; this helper does not assume the parent or domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_uniform_jump_chord_ae_limit
    (f K Y : ℝ≥0 → ℝ) (v d a b q T : ℝ) (hT : 0 ≤ T)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hd : 0 < d) (ha : 0 < a) (hq : 0 ≤ q)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hK : Monotone K)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim f u - f u else 0)
    (hband : ∀ t : ℝ≥0, t ≤ B → v + f t - K t ∈ Icc a b)
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto (fun s => v + f s - K s) (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (n0 : ℕ) (L : ℝ≥0)
    (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1)))
    (hsmall : ∀ n : ℕ, n0 ≤ n →
      d * ((B : ℝ) / ((n + 1 : ℕ) : ℝ)) < min (a / 2) 1) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ f u - Function.leftLim f u ≠ 0}).map
        (fun u : ℝ≥0 => (u, f u - Function.leftLim f u)))
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let V : ℕ → ℕ → ℝ := fun n i => v + f (u n i) - K (u n i)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0
    let F : ℕ → ℝ≥0 × ℝ → ℝ := fun n p => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (V n i - m n i) - w (V n i)) / m n i) * (-p.2) else 0
      else 0
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (V n i + d * h n - m n i) - w (V n i - m n i)) / h n) else 0
      else 0
    let Jdom : ℝ≥0 × ℝ → ℝ := fun p =>
      if 0 < p.1 ∧ p.1 ≤ B ∧ p.2 < 0 then (L : ℝ) * (-p.2) else 0
    ∀ᵐ p ∂NX, Tendsto (fun n => F n p) atTop (nhds (J p)) := by sorry
