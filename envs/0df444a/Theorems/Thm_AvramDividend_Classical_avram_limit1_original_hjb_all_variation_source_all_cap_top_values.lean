-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_hjb_all_variation_source_all_cap_top_values
-- name    : AvramDividend.Classical.avram_limit1_original_hjb_all_variation_source_all_cap_top_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:20:45.824626+00:00
-- url     : https://prove2.me/theorems/ec23873e-03b2-4ecd-9a9b-c9801987b0e9
-- title:
--   Original BV/UBV HJB and finite-clock residual witnesses control capped and unrestricted values
-- statement:
--   For any x >= 0 and capped admissible original process dividend strategy D, assume genuine source-exact stopped W, closed Iic cash, discounted terminal payoff, integrable real cash and original centred HJB residual witnesses at every positive integer horizon. The independent Proved local_verification_hjb_implies_components derives w' >= 1 from the original HJB equality; the pending LIMIT-1 all-BV/UBV source-to-dividendValue theorem uses these original stochastic witnesses as explicit premises. Finally the independently Proved local_verification_from_uniform_strategy_bound converts all admissible-strategy dividendValue bounds into both valueFunctionLe and, if C=top, the unrestricted valueFunction. Unlike the original UBV-only helper f12c6db9, this covers BV C1 and UBV C2, including x=0 under explicit source witnesses. No stochastic estimates are invented or terminal vanishing imposed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_hjb_all_variation_source_all_cap_top_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (hEvidence : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ k : ℕ, 0 < k →
      ∃ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
        (∀ ω, τ ω =
          (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) ∧
        Measurable (fun ω => (τ ω : ℝ)) ∧
        (∀ ω, W ω = if τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω = (∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        Integrable Cash P ∧
        (∃ M G H : Ω → ℝ,
          Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
          (∫ ω, M ω ∂P) = 0 ∧
          (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
          (∀ᵐ ω ∂P, Term ω + Cash ω ≤
            w x + M ω + G ω + H ω))) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
