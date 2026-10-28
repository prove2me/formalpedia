-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_discounted_killed_exponential_reflected_pair_ws01a
-- name    : AvramDividend.Classical.chat04_true_discounted_killed_exponential_reflected_pair_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:48:16.207916+00:00
-- url     : https://prove2.me/theorems/1e0c928a-a7da-4a5c-8a41-f27c4c1917c6
-- title:
--   Genuine discounted half-line killed exponential reward via the reflected-pair law
-- statement:
--   For the actual spectrally negative Lévy path and an independent Exp(p) time, discounting its lower-killed q-scale reward at rate q and multiplying by p+q equals p times the undiscounted lower-killed reward under Exp(p+q). Identify that right-hand side with the true (negative running infimum, terminal drawdown) pushforward law at the shifted exponential time. The assertion is valid for all initial reserves and uses no independent Wiener–Hopf factors, no two-sided exit identity and no stochastic scale harmonicity.
-- source:
--   Canonical Proved stochastic exponential-clock Tonelli 846f9b05, genuine exponential pair pushforward 06a1bccb, exact rate-shift lintegral 61f61f32 and pathwise infimum measurability ae09696f. A private generic product rate-shift proof is in the submitted solution, not a separate catalogue theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_discount_rate_shift_lintegral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_true_discounted_killed_exponential_reflected_pair_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-(q * z.2))) *
          (if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
           then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
           else (0 : ℝ≥0∞))
        ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    ENNReal.ofReal p *
      (∫⁻ a : ℝ × ℝ,
        if a.1 ≤ x then ENNReal.ofReal (W (x - a.1 + a.2))
        else (0 : ℝ≥0∞)
        ∂((P.prod (ProbabilityTheory.expMeasure (p + q))).map
          (fun z : Ω × ℝ =>
            (-sInf {y : ℝ | ∃ s : ℝ≥0,
                      s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
             X.X (Real.toNNReal z.2) z.1 +
               -sInf {y : ℝ | ∃ s : ℝ≥0,
                         s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) := by sorry
