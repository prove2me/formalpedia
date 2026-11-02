-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_zero_boundary_expected_budget_without_terminal_sign_premise
-- name    : AvramDividend.Classical.avram_wave8_ubv_original_zero_boundary_expected_budget_without_terminal_sign_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:05:55.444564+00:00
-- url     : https://prove2.me/theorems/1e0a2817-1e7b-4709-9d47-ef8a0c69a660
-- title:
--   Original UBV expected stopped Ito dividend budget with zero-boundary terminal sign discharged
-- statement:
--   For the actual original SpectrallyNegativeLevy P F and actual admissible D, retain exactly Chat 06's bounded right-continuous source stopping time, W/Cash/Term/M/G/H decomposition, cash finiteness, integrability, martingale-centering and nonpositive residual premises. Remove Chat 06's explicit a.e. nonnegative terminal Term premise, since it follows unconditionally from the corrected core's w(0)>=0, upper-cap, interior C² and derivative hypotheses and the accepted exact piecewise original reserve sign theorem, including creeping and overshoot. Then apply the now Proved Chat 06 assembly to obtain both real expected stopped inequalities. This bridge does not reproduce Itô–Meyer or Stieltjes integration.
-- source:
--   Accepted zero-boundary exact terminal sign 0eb5420e-1c79-4d2e-b7d1-f3030b0bf5e7 and now Proved Chat 06 expected stopped budget b02af371-7a57-4d30-9a67-a2a03ebab34b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_stopped_expected_budget_from_ito_decomposition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_ubv_original_zero_boundary_expected_budget_without_terminal_sign_premise
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
    (hCashFinite : ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGnonpos : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hHnonpos : ∀ᵐ ω ∂P, H ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      Term ω + Cash ω = w x + M ω + G ω + H ω) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
      (∫ ω, Cash ω ∂P) ≤ w x := by sorry
