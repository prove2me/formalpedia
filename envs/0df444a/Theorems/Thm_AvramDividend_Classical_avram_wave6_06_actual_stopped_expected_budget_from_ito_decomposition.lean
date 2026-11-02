-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition
-- name    : AvramDividend.Classical.avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:33:01.823579+00:00
-- url     : https://prove2.me/theorems/b02af371-7a57-4d30-9a67-a2a03ebab34b
-- title:
--   Original ruin-stopped controlled Ito-Meyer expected budget from an explicit centred same-source decomposition
-- statement:
--   For the actual original spectrally negative Levy process and an admissible dividend strategy, take a bounded localised right-continuous-filtration stopping time no later than ruin. The terminal reserve uses post-dividend reserves before ruin, or the ruin reserve at ruin. Cash is exactly the discounted integral against the original dividend measure, with an explicit finiteness premise. If a separate genuine same-path Ito-Meyer theorem supplies an almost-sure equality of terminal plus cash with initial value, an integrable centred martingale and two integrable nonpositive drift/control remainders, then the expected terminal-plus-cash and expected cash are each bounded by the initial supersolution. The chain identity is an EXPLICIT unproved hypothesis, never inferred. This theorem proves only the expectation/terminal-discarding implication.
-- source:
--   Conditional expectation bridge for Avram–Palmowski–Pistorius Proposition 4(i), equations (5.11)–(5.13), downstream of the genuine original-process controlled Ito-Meyer identity. The statement preserves source X,D, right-continuous filtration stop, original ruin time, and original dividendMeasure, and corrects endpoint payment double counting by postpayment terminal reserve. Missing same-source stochastic identity is hIto and must be independently proved. Not a replacement for BV or corrected UBV stochastic cores.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤)
    (w : ℝ → ℝ)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
      (∫ ω, Cash ω ∂P) ≤ w x := by sorry
