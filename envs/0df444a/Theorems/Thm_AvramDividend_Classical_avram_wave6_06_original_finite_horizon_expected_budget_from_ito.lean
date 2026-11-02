-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_finite_horizon_expected_budget_from_ito
-- name    : AvramDividend.Classical.avram_wave6_06_original_finite_horizon_expected_budget_from_ito
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:32:49.714753+00:00
-- url     : https://prove2.me/theorems/231dd4da-d732-49c0-a841-49d84d53637c
-- title:
--   Original bounded ruin-stopped finite-horizon terminal and dividend expectation from the source Ito identity
-- statement:
--   For the original spectrally negative Lévy process, original admissible dividend strategy and its ruin time, and any bounded right-continuous-filtration stopping time before ruin, derive both the expected discounted terminal-plus-complete-Stieltjes-cash budget and the expected dividend-only budget. Preserve original paymentTimes, dividendMeasure and the correct post-dividend terminal reserve before ruin. Hypotheses w(0)≥0, w=0 on negatives, and w nonnegative on positives imply terminal nonnegative. Real cash integrability is automatic from the integrable source stopped Ito decomposition. A.e. finiteness of the closed random-clock source Stieltjes integral follows from the existing deterministic-horizon original process result. The ONLY remaining stochastic bridge is the explicitly assumed original same-path hIto identity together with its integrable centred M and sign remainders; the theorem does not claim the identity itself.
-- source:
--   Source-faithful finite-horizon expectation theorem downstream of explicit missing stochastic hIto. Integrates newly Proved original random clock Stieltjes finiteness and automatic cash integrability, removing two extra conditional hypotheses of b02af371. For the actual Avram–Palmowski–Pistorius Proposition 4(i) (5.11)-(5.13), the correct inclusive endpoint requires postpayment terminal reserve, and w(0)≥0 is preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_finite_horizon_expected_budget_from_ito
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
      ((∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
        (∫ ω, Cash ω ∂P) ≤ w x) := by sorry
