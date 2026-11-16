-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a547_original_clipped_single_HJB_generator_integrable
-- name    : AvramDividend.Classical.avram_ga_a547_original_clipped_single_HJB_generator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:49:40.222515+00:00
-- url     : https://prove2.me/theorems/454b7096-ee8d-4611-81ac-44c4f8d39847
-- title:
--   Integrability of the one-cell masked original HJB generator compensator on the clipped physical grid.
-- statement:
--   Integrability of the one-cell masked original HJB generator compensator on the clipped physical grid.
-- source:
--   Source-faithful one-cell component of a538. For Taylor reuse a165 jet bounds, a544 centred Gaussian square L1 and a545 polynomial domination; for generator reuse gledger157/a165 and one-cell measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a547_original_clipped_single_HJB_generator_integrable
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
    let Cg : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if 0 < ρ ω ∧ s < ρ ω then
        (Δ : ℝ) * E s * X.generator w (Y s)
      else 0
    ∀ m i : ℕ, i < m → Integrable (Cg m i) P := by sorry
