-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_source_hjb_budget_conditional_ito
-- name    : AvramDividend.Classical.avram_wave6_06_original_zero_clock_source_hjb_budget_conditional_ito
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:39:48.82321+00:00
-- url     : https://prove2.me/theorems/a96fe8c5-5c58-479f-a2ab-30aecb48df94
-- title:
--   Full original source HJB finite-horizon expected dividend bound with correct zero-clock right-payment terminal
-- statement:
--   The final zero-clock-corrected source expected verification consumer: exactly original X, admissible D, ruinTime, q>0, capped w with w(0)>=0 and zero below 0, source max(generator-qw,1-w')=0, BV C1/UBV C2 separately, bounded original right-continuous filtration stopping τ<=ruin. The terminal W is the POST-right-dividend reserve when τ=0 OR τ<ruin, and riskProcess at strictly positive ruin; this avoids double-counting the time-zero right payment atom that paymentTimes includes even when ruinTime=0. Under explicitly given same-source stopped Ito hIto, integrability, zero-mean martingale and joint generator-plus-Stieltjes nonpositive remainder, prove real terminal-plus-cash and cash-only budgets and exact inclusive-clock ENNReal expected dividends <= w(x). No global w>=0 hypothesis, no hidden stochastic identity. All non-stochastic steps are fully composed from separately Proved source results.
-- source:
--   Avram-Palmowski-Pistorius Prop 4(i) (5.11)-(5.13), source time-zero atom and zero-clock postpayment convention; exact HJB max equation and boundary w(0)≥0. Imports source 9cf successor zero-clock terminal, e145, 1f and 89e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_zero_clock_source_hjb_budget_conditional_ito
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGHnonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    Integrable Cash P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
      (∫ ω, Cash ω ∂P) ≤ w x ∧
      (∫⁻ ω, ∫⁻ s in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by sorry
