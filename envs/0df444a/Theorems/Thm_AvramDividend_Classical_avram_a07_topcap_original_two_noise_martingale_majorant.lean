-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_topcap_original_two_noise_martingale_majorant
-- name    : AvramDividend.Classical.avram_a07_topcap_original_two_noise_martingale_majorant
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T16:25:22.431091+00:00
-- url     : https://prove2.me/theorems/df0ddfa2-b183-44e6-9358-97750b03f357
-- title:
--   Original top-cap stopped Ito-Meyer two-noise physical majorant
-- statement:
--   Establish the source-exact original probability-space stopped Ito-Meyer cash ledger: construct the original Gaussian and compensated jump residuals, prove their integrability, time-zero conditional centring and an almost sure upper bound on the actual ruin-clipped discounted cash reward. Explicitly account for σ=0, ruin atoms and top-cap C=∞. This theorem has no dependency on the top-cap eventwise consequence, avoiding a circular route.
-- source:
--   Physical source obligation of A07 positive-clock top-cap stopped Ito-Meyer verification; represents the required independent stochastic ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_topcap_original_two_noise_martingale_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤) :
    ∃ MG MJ : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ w x + MG ω + MJ ω) := by sorry
