-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a390_original_true_crossing_HJB_uniform_abs_vanish
-- name    : AvramDividend.Classical.avram_ga_a390_original_true_crossing_HJB_uniform_abs_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T14:17:21.14544+00:00
-- url     : https://prove2.me/theorems/e1f3c9a8-8bea-4529-97e2-150feba16149
-- title:
--   Original strict Gaussian stop-crossing HJB compensator has a vanishing uniform absolute envelope
-- statement:
--   On the original true stopped Gaussian physical mesh crossing cell, the absolute compensated generator/HJB Gaussian term is uniformly bounded by an almost-surely vanishing nonnegative mesh envelope.
-- source:
--   Exact source-specific a382 uniform crossing-cell positive mesh error decomposed into pathwise spatial modulus (a106) and small HJB compensator (a112).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a390_original_true_crossing_HJB_uniform_abs_vanish
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
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : Ω → ℝ≥0 → ℝ := fun ω t => x + X.X t ω - rightLimit D t ω
    let Hcell : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let R : ℝ := X.X (s m i + Δ m) ω - X.X (s m i) ω
      let Z : ℝ := R - (Δ m : ℝ) * X.c
      E (s m i) * (deriv w (Y ω (s m i)) * Z +
        (iteratedDeriv 2 w (Y ω (s m i)) / 2) *
          (Z^2 - (Δ m : ℝ) * X.σ^2)) +
        (Δ m : ℝ) * E (s m i) * X.generator w (Y ω (s m i))
    ∃ B : ℕ → Ω → ℝ,
      (∀ (m : ℕ) (ω : Ω), 0 ≤ B m ω) ∧
      (∀ (m : ℕ) (ω : Ω) (i : ℕ), i < m →
        s m i < ρ ω → ρ ω ≤ s m (i + 1) →
        |Hcell m i ω| ≤ B m ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun m => B m ω) atTop (nhds (0 : ℝ))) := by sorry
