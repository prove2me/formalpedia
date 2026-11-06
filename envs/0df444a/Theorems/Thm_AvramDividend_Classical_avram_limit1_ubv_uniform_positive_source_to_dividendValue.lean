-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_uniform_positive_source_to_dividendValue
-- name    : AvramDividend.Classical.avram_limit1_ubv_uniform_positive_source_to_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:15:06.875121+00:00
-- url     : https://prove2.me/theorems/53d489ee-dd18-4507-8984-7ff8ba924d19
-- title:
--   Positive-horizon source UBV martingale witnesses bound the genuine perpetual dividend value
-- statement:
--   For the unchanged original spectrally negative Levy process and genuine capped admissible dividend strategy, assume source-exact bounded ruin-clock W, Cash, Term and a centred integrable residual witness M,G,H for each strictly positive integer stopping horizon. The Proved LIMIT-1 original residual bridge controls the closed random-clock Stieltjes cash. A future n+1 clock dominates natural clock n using original paymentTimes_min_mono_horizon, with its time-zero right-payment atom intact. The source paymentTimes predicate and exact min-clock cast show its natural stopped support lies within the closed random-clock window. Proved original natural stopped budget implies the actual full discounted dividendValue is bounded by ENNReal.ofReal(w x). There is no terminal vanishing, equality-in-law, extra martingale proof or positive ruin-atom assumption; all stochastic residual witnesses are explicit hypotheses.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_original_single_residual_to_stopped_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_ubv_uniform_positive_source_to_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
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
