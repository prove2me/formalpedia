-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop18_original_physical_compact_clock_exhaustion
-- name    : AvramDividend.Classical.avram_gtop18_original_physical_compact_clock_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:20:59.858375+00:00
-- url     : https://prove2.me/theorems/22bf1d41-5455-4c22-9889-3cfcfa260303
-- title:
--   Genuine zero-jump Gaussian compact reserve stopping clocks exhaust the original stopped horizon
-- statement:
--   Necessary original-process geometric child of 61cdc38d. Establish a monotone family of genuine right-continuous filtration stopping times below the original sigma, with almost-sure cofinality and two-sided prepayment reserve bounds on every strict prefix. The zero-volatility-free Brownian first-zero-versus-ruin argument, initial right payment and clipped horizon must be handled, with no alternative process or arbitrary stopping-time floor.
-- source:
--   Root-connected exact reduction of Open 61cdc38d-6371-4c61-b8e6-704e38c04057, preserving original X,D, sigma and ruin time. Separate reward measurability and convergence is delegated to its sibling.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop18_original_physical_compact_clock_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (ρ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, ρ j ω ≤ σ ω) ∧
      (∀ ω, Monotone (fun j : ℕ => ρ j ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω))) ∧
      (∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
        riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) := by sorry
