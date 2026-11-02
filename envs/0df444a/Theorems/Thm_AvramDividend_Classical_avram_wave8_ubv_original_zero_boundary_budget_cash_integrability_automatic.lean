-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_zero_boundary_budget_cash_integrability_automatic
-- name    : AvramDividend.Classical.avram_wave8_ubv_original_zero_boundary_budget_cash_integrability_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:44:49.498431+00:00
-- url     : https://prove2.me/theorems/51c6c91d-4a1f-40d2-82d9-f40c55d89cfa
-- title:
--   Original UBV zero-boundary stopped dividend budget automatically supplies integrable cash
-- statement:
--   For the actual original SpectrallyNegativeLevy process, source filtration and admissible D, discharge terminal sign from the Proved zero-boundary piecewise reward theorem, and a.e. bounded stopped dividend finiteness from the already Proved Chat06 original bounded random clock Stieltjes finiteness. Apply the now Proved Chat06 automatic cash-integrability theorem to infer Integrable Cash and both real expected stopped Ito dividend budgets without postulating cash integrability. Retain integrability of Term/M/G/H, centred M, nonpositive residuals and exact same-source Ito identity explicitly. No derivative-at-zero, extra cap or boundary assumption; neither Ito-Meyer nor Stieltjes integration repeated.
-- source:
--   Proved original cash integrability from Ito 1f065cfc-8c6a-4896-a3b2-686c454d6311; accepted zero sign 0eb5420e-1c79-4d2e-b7d1-f3030b0bf5e7; Proved source bounded cash finiteness e1455beb-b5b2-4e36-afc2-d20336b64128.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cash_integrability_and_budget_from_ito

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_ubv_original_zero_boundary_budget_cash_integrability_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
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
