-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_preruin_localised_original_stieltjes_reward_full_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_preruin_localised_original_stieltjes_reward_full_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:52:14.340007+00:00
-- url     : https://prove2.me/theorems/2403348e-8069-4198-8674-be796a16be2d
-- title:
--   Full original discounted Stieltjes reward at an arbitrary stopped clock dominated by true ruin
-- statement:
--   For any pathwise clock τ at or before the true source-X ruin time, a finite horizon T and an interior cap localisation along τ payment times, the entire original stopped Stieltjes reward is bounded by a sum of genuine chronological HJump secants and the atomless Stieltjes gradient measure of the actual dividend strategy. The residual measure includes singular-continuous and absolutely continuous payments; there is no atom-only assumption or dividend density. The HJump hypothesis has the exact corrected t=0 or t<ruinTime scope, and τ can also impose a cap-interior localisation clock. There is no stochastic local martingale or generator identity here.
-- source:
--   04-B source-X pathwise localisation and complete Stieltjes dividends under corrected HJump scope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_stopped_full_stieltjes_control_correction

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_preruin_localised_original_stieltjes_reward_full_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞)
    (hτ : τ ≤ ruinTime X x D ω) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
      (∑' t : A,
        ENNReal.ofReal
          (w (riskProcess X x D (t : ℝ).toNNReal ω) -
            w (riskProcess X x D (t : ℝ).toNNReal ω -
              (rightLimit D (t : ℝ).toNNReal ω -
                D (t : ℝ).toNNReal ω))) *
        (paymentTimes τ).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-q * s)) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by
  sorry
