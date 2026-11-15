-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a264_original_combined_fullcell_small_raw_increment_positive_budget
-- name    : AvramDividend.Classical.avram_ga_a264_original_combined_fullcell_small_raw_increment_positive_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:54:02.759781+00:00
-- url     : https://prove2.me/theorems/116faa31-0b02-4837-acc3-3e832d3238eb
-- title:
--   True original stopped Gaussian combined small-raw-increment positive source has arbitrarily small expected budget under refining physical mesh
-- statement:
--   With exactly the original zerojump Gaussian stopped physical fullcell source of a216, keep only increments of absolute raw size below δ. For any η>0 choose a Taylor modulus δ>0 and sufficiently refined physical mesh so that the positive expected combined small-cell source is at most η, while every finite-mesh masked positive source remains integrable. Source-specific inputs are proved one-sided Taylor a194, original Gaussian combined one-cell inequality a236, true physical raw quadratic expected bound a240, and original Hessian cross L1 a150 plus the first-order discount-width decay. Together with the complementary true large-cell expected L1 a263 this closes original a216 via the exact finite-mesh partition.
-- source:
--   Original a216 exact physical fullcell source small mask |R|<δ; a194,a236,a240,a150,a206

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a264_original_combined_fullcell_small_raw_increment_positive_budget
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
    let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ |R i| < δ then F i else 0
    (∀ δ : ℝ, 0 < δ → ∀ m, Integrable
        (fun ω => max (Small δ m ω) 0) P) ∧
      ∀ η : ℝ, 0 < η →
        ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ,
          ∀ m : ℕ, k ≤ m →
            (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by sorry
