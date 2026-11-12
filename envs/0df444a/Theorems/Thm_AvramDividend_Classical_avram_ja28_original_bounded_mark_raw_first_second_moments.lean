-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments
-- name    : AvramDividend.Classical.avram_ja28_original_bounded_mark_raw_first_second_moments
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T21:55:06.650487+00:00
-- url     : https://prove2.me/theorems/4106f6a7-d069-4504-a840-d5b32edca1d5
-- title:
--   First and second raw moments of a bounded marked Poisson integral on actual finite negative strips
-- statement:
--   Original finite-activity negative marked jump measure: a bounded measurable real weight g has first raw moment t times the Levy intensity integral and second raw moment its squared mean plus t times the weighted square intensity. This supplies the true source martingale isometry after elementary centering. Requires arbitrary within-strip Borel marked factorial pair mean, not just harmonic annulus counts.
-- source:
--   Direct physical Poisson moment core of 2a4be8dd and ec5fe7b6. Original count moment inputs d42bd524, eac4c5a9 and 6ea0212e; finite-activity source count L2 from 85768b34.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja28_original_bounded_mark_raw_first_second_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (g : ℝ → ℝ),
      Measurable g →
      (∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), |g z| ≤ 1) →
      ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let J : Ω → ℝ := fun ω =>
        ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
      let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
      let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
      Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
        (∫ ω, J ω ∂P) = r ∧
        (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q := by sorry
