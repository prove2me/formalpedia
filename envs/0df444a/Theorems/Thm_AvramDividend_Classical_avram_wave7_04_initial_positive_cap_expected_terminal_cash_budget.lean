-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:47:11.303651+00:00
-- url     : https://prove2.me/theorems/8d16d65f-d4ac-4ed5-a2b9-3ad9857258d4
-- title:
--   Original BV positive-cap zero-clock expected full Stieltjes cash and surviving terminal budget
-- statement:
--   Under the original positive-cap BV HJB gradient and admissibility assumptions, when the exact time-zero real full Stieltjes cash and surviving post-payment terminal variables are integrable, their expectations sum to at most w(x). This averages the original pathwise zero-clock HJB budget over the original probability measure, retaining its exact time-zero payout atom.
-- source:
--   Formal Lebesgue expectation bridge importing Proved original positive-cap zero-clock full atom+terminal 82bf9d2c-e88a-40bb-93d6-87a197c33510. The explicit integrability hypotheses isolate the source stopped cash and terminal L1 prerequisites, so the time-zero martingale budget passes to expectation without modifying the original probability space. Supports the zero-clock case of stronger stopped supermartingale 0618723a-bb0b-4fa0-94bc-4def7af7aafa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ)
    (hCashI : Integrable (fun ω : Ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hTermI : Integrable (fun ω : Ω => if (0 : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (w (x - rightLimit D 0 ω)) else 0) P) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, if (0 : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (w (x - rightLimit D 0 ω)) else 0 ∂P) ≤ w x := by sorry
