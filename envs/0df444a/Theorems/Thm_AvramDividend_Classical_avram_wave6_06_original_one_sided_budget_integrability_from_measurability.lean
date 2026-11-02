-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_budget_integrability_from_measurability
-- name    : AvramDividend.Classical.avram_wave6_06_original_one_sided_budget_integrability_from_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:11:26.123387+00:00
-- url     : https://prove2.me/theorems/30b2e334-3874-4610-8a53-9fdffa78bb74
-- title:
--   One-sided original ruin-stopped HJB budget yields full cash and terminal integrability from source measurability
-- statement:
--   For the actual admissible original dividend and ruin clock, positive cap, boundary w(0)>=0 and the separate BV C1/UBV C2 test regularity, the source terminal selector is nonnegative and the exact original complete discounted Stieltjes cash is nonnegative. If both are a.e. strongly measurable and satisfy an a.e. one-sided Ito-Meyer bound by the integrable original martingale-plus-drift terms, both are integrable automatically. Thus the one-sided expected budget bridge need only source measurability instead of assuming these two integrabilities independently. This is a non-stochastic order/integrability consequence; the one-sided Ito inequality and source measurability are still explicit premises.
-- source:
--   Avram Proposition 4(i), Eq. (5.11)-(5.13). Uses Proved actual zero-clock endpoint nonnegativity 9bd8e442 and Mathlib Integrable.mono with exact pinned signature.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_one_sided_budget_integrability_from_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hUpper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    Integrable Term P ∧ Integrable Cash P := by sorry
