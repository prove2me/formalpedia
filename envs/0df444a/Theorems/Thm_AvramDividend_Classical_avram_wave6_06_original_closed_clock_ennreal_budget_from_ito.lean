-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_closed_clock_ennreal_budget_from_ito
-- name    : AvramDividend.Classical.avram_wave6_06_original_closed_clock_ennreal_budget_from_ito
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:20:36.429427+00:00
-- url     : https://prove2.me/theorems/d22be5e6-36bf-483b-b0ce-f413525a3cf4
-- title:
--   Exact original inclusive ruin-stopped expected discounted dividends from genuine conditional Ito source identity
-- statement:
--   The original Lévy X, original admissible D, ruin sigma, bounded right-continuous filtration stop tau before ruin, corrected post-right-dividend W, and original closed random-clock dividendMeasure cash are preserved literally. With w nonnegative including w(0)>=0 and negative-reserve boundary zero, integrate an explicitly given genuine same-path stopped Ito decomposition with integrable zero-mean stochastic part and nonpositive generator/control remainders. Derive integrability, expected terminal plus cash ≤ w(x), expected cash ≤ w(x), and the exact nested ENNReal expected discounted dividend bound ≤ ENNReal.ofReal(w(x)). The stochastic identity hIto and its sign/mean-zero components are explicit outstanding assumptions, not asserted results.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i), eqs (5.11)-(5.13), original source cash including stopped endpoint payment; deterministic expectation and ENNReal bridge only, pending actual mixed same-source stopped Ito-Meyer identity and BV/UBV derivation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_budget_to_ennreal

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_closed_clock_ennreal_budget_from_ito
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
    (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_pos : ∀ y : ℝ, 0 < y → 0 ≤ w y)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    Integrable Cash P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
      (∫ ω, Cash ω ∂P) ≤ w x ∧
      (∫⁻ ω, ∫⁻ s in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by sorry
