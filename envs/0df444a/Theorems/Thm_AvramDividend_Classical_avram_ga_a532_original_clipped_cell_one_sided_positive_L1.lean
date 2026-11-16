-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a532_original_clipped_cell_one_sided_positive_L1
-- name    : AvramDividend.Classical.avram_ga_a532_original_clipped_cell_one_sided_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:18:39.825049+00:00
-- url     : https://prove2.me/theorems/ae9f4357-8f5a-4716-9e10-7a4e9f4e0510
-- title:
--   Every individually masked original clipped Gaussian spatial cell has an integrable positive part
-- statement:
--   Under the original zero-jump Gaussian, stopping and compact-prefix hypotheses, each one-cell term of the source-faithful clipped postpayment spatial Taylor and generator residual is almost-everywhere strongly measurable and has an integrable positive part, after excluding the zero-clock atom. This is a one-sided cell estimate without a negative-tail moment assumption on the value function.
-- source:
--   One-sided a257 HJB exponential upper bound, proved gledger69 stopped exponential moment, a530 positive-part envelope, compact coefficient bounds, and proved a258 finite combined-cell majorant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a532_original_clipped_cell_one_sided_positive_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let W : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      if 0 < ρ ω then
        E (v (i + 1)) * (w (Z i) - w (Y (v i))) -
          (if s < ρ ω then
            E s * (deriv w (Y s) * z +
              (iteratedDeriv 2 w (Y s) / 2) *
                (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0) -
          (if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
      else 0
    ∀ m i : ℕ, i < m →
      AEStronglyMeasurable (W m i) P ∧
      Integrable (fun ω => max (W m i ω) (0 : ℝ)) P := by sorry
