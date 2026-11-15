-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a415_original_inclusive_crossing_spatial_uniform_cell_modulus
-- name    : AvramDividend.Classical.avram_ga_a415_original_inclusive_crossing_spatial_uniform_cell_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:26:32.080907+00:00
-- url     : https://prove2.me/theorems/5c862a9f-301b-4cf7-8ae5-0f0dbd917f5c
-- title:
--   Original strict Gaussian crossing spatial value increment is uniformly vanishing per physical cell
-- statement:
--   On almost every bounded positive pre-stop reserve prefix, the original stopped discounted spatial value increment over every genuine inclusive Gaussian crossing subcell becomes uniformly small as its physical mesh width shrinks.
-- source:
--   Proved original compact positive postpayment prefix gledger137, deterministic C2 local Lipschitz a204 and a414 source Gaussian subcell modulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a415_original_inclusive_crossing_spatial_uniform_cell_modulus
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
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ i : ℕ, i < m →
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        s < ρ ω → ρ ω ≤ s + Δ →
          |Real.exp (-(q * (ρ ω : ℝ))) *
            (w (x + X.X (ρ ω) ω - rightLimit D s ω) -
             w (x + X.X s ω - rightLimit D s ω))| < ε := by sorry
