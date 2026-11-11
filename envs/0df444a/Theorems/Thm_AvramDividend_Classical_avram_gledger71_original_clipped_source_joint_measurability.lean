-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger71_original_clipped_source_joint_measurability
-- name    : AvramDividend.Classical.avram_gledger71_original_clipped_source_joint_measurability
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T01:36:44.360438+00:00
-- url     : https://prove2.me/theorems/6b3d4114-e79a-4d2e-87a6-f98eb2513a84
-- title:
--   Original stopped Gaussian source observations, stopping clocks and right payouts are measurable
-- statement:
--   The original stopped-grid sample observables are a.e. measurable, clipped deterministic grid clocks are measurable stopping times, right-limit payouts are nonnegative, and the bounded ruin-clipped clock admits finite endpoint control. The only spatial regularity needed is derived on the physical nonnegative reserve range.
-- source:
--   Necessary distinct physical sub-obligation for root-connected gledger68, which feeds accepted gledger53. Proven gledger67 supplies stopped clock measurability; gledger54,63,65,70 supply envelope ingredients.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger71_original_clipped_source_joint_measurability
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
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let S : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))
      AEStronglyMeasurable S P ∧
      (∀ θ : ℝ, ∀ i : ℕ,
        AEStronglyMeasurable (fun ω => Real.exp (θ * Z i ω)) P) ∧
      (∀ i : ℕ, Measurable (fun ω => (v i ω : ℝ))) ∧
      (∀ i : ℕ, IsStoppingTime 𝓕.rightCont (fun ω => (v i ω : WithTop ℝ≥0))) ∧
      (∀ i ω, 0 ≤ rightLimit D (v i ω) ω) ∧
      (∀ ω, ρ ω ≤ (n : ℝ≥0)) := by sorry
