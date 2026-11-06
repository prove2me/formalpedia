-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
-- name    : AvramDividend.Classical.avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:17:44.508775+00:00
-- url     : https://prove2.me/theorems/a1f8fa5e-5543-4a49-a8ed-5e8ddfa88baf
-- title:
--   All BV/UBV original stopped residual witnesses bound the genuine perpetual dividendValue
-- statement:
--   For each strictly positive original ruin-clipped integer clock, assume actual postpayment W, discounted closed Stieltjes Cash, terminal Term, integrable Cash and an explicit centred signed original-process residual M/G/H. The new source-exact LIMIT-1 all-variation single residual bridge controls closed cash for BV and UBV without claiming martingale results or terminal vanishing. For each natural horizon n, choose evidence at n+1 and apply the original Proved paymentTimes_min_mono_horizon. The genuine time-zero right payment stays inside the closed Iic clock. Monotonicity of inner and outer ENNReal lintegrals passes the budget to the original natural stopped paymentTimes. Finally Proved avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue yields perpetual dividendValue ≤ ENNReal.ofReal (w x). No equality in law, circular canonical parent, or extra a.e. assumption.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_all_variation_zero_clock_residual_to_closed_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_uniform_source_to_full_dividendValue_bv_ubv
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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hEvidence : ∀ k : ℕ, 0 < k →
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
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
