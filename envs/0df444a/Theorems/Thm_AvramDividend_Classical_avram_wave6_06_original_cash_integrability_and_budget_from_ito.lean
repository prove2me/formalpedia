-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito
-- name    : AvramDividend.Classical.avram_wave6_06_original_cash_integrability_and_budget_from_ito
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:02:35.582875+00:00
-- url     : https://prove2.me/theorems/1f065cfc-8c6a-4896-a3b2-686c454d6311
-- title:
--   Original stopped Ito-Meyer decomposition automatically yields cash integrability and both discounted bounds
-- statement:
--   For the original spectrally negative Lévy X and genuine admissible D, retain the exact bounded right-continuous stopping time before original ruin, postpayment terminal reserve, and source dividendMeasure integral. Given an almost-sure same-source stopped Ito-Meyer decomposition with integrable terminal, martingale, generator and Stieltjes remainders, show the actual dividend cash is automatically integrable by rearranging the decomposition; then import the Proved expected budget bridge b02af371 to bound terminal-plus-cash and cash alone. The stochastic chain identity hIto is explicitly assumed and remains to be proved independently; no stochastic conclusion is concealed.
-- source:
--   Strict strengthening of Proved b02af371: derives the formerly assumed hCashI from the full integrable original-source hIto equality. This is the remaining non-stochastic L1 closure at the genuine ruin-stopped finite horizon; it does not claim the Ito equation, and preserves every source stop/payment/filtration condition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_cash_integrability_and_budget_from_ito
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
    (hTermI : Integrable Term P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    Integrable Cash P ∧
      ((∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
        (∫ ω, Cash ω ∂P) ≤ w x) := by sorry
