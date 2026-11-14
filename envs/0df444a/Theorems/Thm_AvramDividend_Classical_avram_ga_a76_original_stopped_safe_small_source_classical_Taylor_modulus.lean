-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
-- name    : AvramDividend.Classical.avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:46:33.055691+00:00
-- url     : https://prove2.me/theorems/98d10442-36c1-4a69-8b64-86ae0950b680
-- title:
--   Original dividend-controlled stopped Gaussian small-source cells have uniformly arbitrarily small classical C2 Taylor spatial error relative to raw quadratic energy
-- statement:
--   For the original stopped dividend-controlled source and its positive compact postpayment reserve prefix, every finite collection of true pre-stop physical source cells with sufficiently small nonzero original raw increments has total ordinary-gradient-and-Hessian second-order spatial Taylor error bounded by epsilon times actual raw quadratic source energy almost surely.
-- source:
--   Direct original b0d9951c safe positive compact C2 Taylor spatial remainder, applies ga_a47 and ga_a75 classical derivative bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbCap : ENNReal.ofReal (b + a / 2) < C)
    (hDiff : ∀ z ∈ Icc (a / 2) (b + a / 2), DifferentiableAt ℝ w z)
    (hBand : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < ρ ω →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ (S : Finset ℕ) (s t : ℕ → ℝ≥0),
        (∀ i ∈ S, s i < ρ ω ∧
          X.X (t i) ω - X.X (s i) ω ≠ 0 ∧
          |X.X (t i) ω - X.X (s i) ω| < δ) →
        let Y : ℕ → ℝ := fun i =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        let Z : ℕ → ℝ := fun i =>
          x + X.X (t i) ω - rightLimit D (s i) ω
        let R : ℕ → ℝ := fun i => X.X (t i) ω - X.X (s i) ω
        |∑ i ∈ S, (w (Z i) - w (Y i) -
          deriv w (Y i) * R i -
          (iteratedDeriv 2 w (Y i) * (R i)^2) / 2)| ≤
          ε * ∑ i ∈ S, (R i)^2 := by sorry
