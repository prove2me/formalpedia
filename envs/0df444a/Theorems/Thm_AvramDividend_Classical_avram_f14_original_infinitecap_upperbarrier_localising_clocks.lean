-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f14_original_infinitecap_upperbarrier_localising_clocks
-- name    : AvramDividend.Classical.avram_f14_original_infinitecap_upperbarrier_localising_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:15:59.582112+00:00
-- url     : https://prove2.me/theorems/7ec2b70b-1ed3-440d-bf7e-5d71c11d9956
-- title:
--   Original UBV infinite-cap adapted bounded-upward-exit localising clocks
-- statement:
--   Construct original filtration stopping times before the exact ruin-capped horizon with terminal Levy path bounded by k+1; as k grows, the clocks equal that horizon eventually for every path. Use the no-positive-jumps and cadlag properties of the original source.
-- source:
--   First-passage-upward original Levy process localisation, a source-exact independent clock input for 1a91b59a, not a generic replaced process.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_f14_original_infinitecap_upperbarrier_localising_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hCtop : C = ⊤) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))) ∧
      (∀ k, Measurable (fun ω => (σ k ω : ℝ))) ∧
      (∀ k ω, σ k ω ≤ τ ω) ∧
      (∀ k ω, X.X (σ k ω) ω ≤ (k : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, σ k ω = τ ω) := by sorry
