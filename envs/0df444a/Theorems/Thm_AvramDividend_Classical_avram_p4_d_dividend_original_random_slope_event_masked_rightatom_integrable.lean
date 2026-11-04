-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_slope_event_masked_rightatom_integrable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_slope_event_masked_rightatom_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:01:49.292904+00:00
-- url     : https://prove2.me/theorems/49069575-20c7-4a8e-a6e9-0fca45e4bc1f
-- title:
--   Path-dependent right-dividend secant cash envelope controls event-masked source atomic L1
-- statement:
--   For a measurable event of original Lévy sample paths, allow the right-dividend secant upper slope K(ω) to vary with the path and require it only where the original path lies in the event. If K≥1 there and the exact stopped Stieltjes Cash product envelope masked to this event is integrable, prove the actual source-ordered countable measurable right-atom signed correction masked to the event is integrable and nonpositive almost surely. The result uses the proved pathwise absolute source atomic budget with a different K for each path, retaining time zero, eligible horizon and simultaneous source/dividend jumps, without globally extrapolating interior derivative regularity.
-- source:
--   Proved fd02394f original true paymentTimes signed absolute cash; Mathlib AEStronglyMeasurable.tsum, indicator and Integrable.mono; original P4-F Cash 0dda1be7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_slope_event_masked_rightatom_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (s : Set Ω) (hs : MeasurableSet s)
    (K : Ω → ℝ) (hK : ∀ ω ∈ s, 1 ≤ K ω)
    (hLocalSecant : ∀ ω ∈ s, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K ω * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal)
    (hEnvelopeI : Integrable (s.indicator (fun ω => (K ω - 1) * Cash ω)) P)
    (hAtomTermMeas : ∀ i : ι,
      AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    let H : Ω → ℝ := fun ω => ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
    Integrable (s.indicator H) P ∧
      (∀ᵐ ω ∂P, s.indicator H ω ≤ 0) := by sorry
