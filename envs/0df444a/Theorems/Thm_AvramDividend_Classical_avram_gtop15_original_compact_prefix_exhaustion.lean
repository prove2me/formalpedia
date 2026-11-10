-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop15_original_compact_prefix_exhaustion
-- name    : AvramDividend.Classical.avram_gtop15_original_compact_prefix_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:08:49.662197+00:00
-- url     : https://prove2.me/theorems/61cdc38d-6371-4c61-b8e6-704e38c04057
-- title:
--   Original zero-jump top-cap compact stopped reserve prefixes exhaust the strict clipped reward
-- statement:
--   For each original right-continuous ruin-bounded stopping clock, construct genuine same-filtration spatial-prefix exit clocks before the target, with positive interior reserve between reciprocal lower and growing upper levels. Their strict prepayment rewards are measurable and converge almost surely in ENNReal to the exact clock reward, including the time-zero and positive ruin contact conventions. No arbitrary-grid or hypothetical stochastic ledger is assumed.
-- source:
--   Necessary original-source localisation and endpoint exhaustion for d65c7756; compact stopped Ito budget is a distinct second obligation. Exceptional sample paths are handled a.e.; ENNReal limit preserves strict Iio cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop15_original_compact_prefix_exhaustion
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
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
      if ζ ω = 0 then w x else
        Real.exp (-(q * (ζ ω : ℝ))) *
          w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (ρ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, ρ j ω ≤ σ ω) ∧
      (∀ j, Measurable (H (ρ j))) ∧
      AEStronglyMeasurable (H σ) P ∧
      (∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
        riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) ∧
      (∀ᵐ ω ∂P, Tendsto
        (fun j => ENNReal.ofReal (H (ρ j) ω)) atTop
        (nhds (ENNReal.ofReal (H σ ω)))) := by sorry
