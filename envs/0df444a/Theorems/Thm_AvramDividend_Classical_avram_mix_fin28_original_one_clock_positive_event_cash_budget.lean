-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_one_clock_positive_event_cash_budget
-- name    : AvramDividend.Classical.avram_mix_fin28_original_one_clock_positive_event_cash_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T15:01:02.408916+00:00
-- url     : https://prove2.me/theorems/52a16569-4e54-497f-8dc9-3395e758ae3e
-- title:
--   Original finite mixed physical stopped Ito source cash budget at one ruin-clipped clock
-- statement:
--   This is the single-clock, exact-original-process stochastic content of the accepted 2545e563 route. For any actual bounded right-continuous filtration stopping clock rho no later than ruin and n, the source reward formed by discounted postpayment terminal w and genuine closed dividend Stieltjes cash satisfies the initial-event positive-clock expected inequality. No arbitrary family of earlier clocks, unrelated source F, or global L1 MG+MJ premise is imposed. Prove by true positive-reserve and spatial localisations, original same-filtration Gaussian and finite negative-jump compensated source martingales, HJB drift and gradient corrections, then source-exact physical limits. Reuse Proved 9afa1813 (bounded local Gaussian gradient) and e8a2fc6a (negative mark reward increment bounded independent of mark size), plus generic original lower-reserve clocks cb3e82b1. Handle initial right payment, strict ruin cash, ruin negative jump and horizon atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin28_original_one_clock_positive_event_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (G : Ω → ℝ)
    (hGsource : ∀ ω, G ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨
              (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {ω : Ω | ρ ω ≠ 0}, G ω ∂P) ≤
        w x * (P (A ∩ {ω : Ω | ρ ω ≠ 0})).toReal := by sorry
