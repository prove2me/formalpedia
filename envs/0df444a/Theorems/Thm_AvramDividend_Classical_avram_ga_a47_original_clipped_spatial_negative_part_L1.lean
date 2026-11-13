-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a47_original_clipped_spatial_negative_part_L1
-- name    : AvramDividend.Classical.avram_ga_a47_original_clipped_spatial_negative_part_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T17:13:36.960202+00:00
-- url     : https://prove2.me/theorems/656dff17-1151-45b5-95f4-75ad4f94e293
-- title:
--   Original clipped physical Gaussian Taylor error negative part vanishes in L1
-- statement:
--   For the unchanged original spectrally negative Levy process, right-limit dividend strategy and stopped Gaussian grid, the negative part max(-B_m,0) of the full spatial postpayment Taylor/generator residual is integrable and has vanishing expectation as mesh size tends to zero. This is a necessary physical signed-error estimate for deriving the original absolute L1 residual c47f646c.
-- source:
--   Mirror necessary child of c47f646c, complementary to gledger178 5318a4dc-2908-4f4d-a982-969fdda144ab.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a47_original_clipped_spatial_negative_part_L1
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
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (∑ i ∈ Finset.range (m + 1),
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := Y s
          let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          E s * (deriv w y * z +
            (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-B m ω) (0 : ℝ)) P ∧
      (∫ ω, max (-B m ω) (0 : ℝ) ∂P) ≤ ε := by sorry
