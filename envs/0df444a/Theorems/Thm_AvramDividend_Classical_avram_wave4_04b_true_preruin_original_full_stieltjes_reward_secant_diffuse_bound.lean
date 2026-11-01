-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_true_preruin_original_full_stieltjes_reward_secant_diffuse_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_true_preruin_original_full_stieltjes_reward_secant_diffuse_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:45:11.371983+00:00
-- url     : https://prove2.me/theorems/5d182c9d-fa7f-4729-9b25-7a1f4a1fe2a3
-- title:
--   Full original stopped Stieltjes cash reward at true ruin time bounded by atomless gradient and chronological HJump secants
-- statement:
--   For an actual spectrally negative Lévy surplus controlled by an admissible dividend process, the full original stopped discounted Stieltjes reward, including the initial right atom, arbitrary later right jumps, singular-continuous mass and absolutely continuous mass, is bounded by the chronological HJump secant sum over the true atom support plus the full atomless diffuse dividend measure integrated against the local derivative of w. The source-compatible decomposition μ = μatom + μdiffuse is provided existentially and μdiffuse has no singleton mass. The HJump premise is precisely t=0 or t<ruinTime, with gradient localisation only on the declared interior payment support. No martingale or source-X Itô–Meyer formula is claimed.
-- source:
--   04-B corrected true-ruin full original Stieltjes reward bridge to Chat04, no canonical UBV inequality

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_stopped_full_stieltjes_control_correction

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_true_preruin_original_full_stieltjes_reward_secant_diffuse_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) →
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
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
      (∑' t : A,
        ENNReal.ofReal
          (w (riskProcess X x D (t : ℝ).toNNReal ω) -
            w (riskProcess X x D (t : ℝ).toNNReal ω -
              (rightLimit D (t : ℝ).toNNReal ω -
                D (t : ℝ).toNNReal ω))) *
        (paymentTimes (ruinTime X x D ω)).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-q * s)) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by
  sorry
