-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_exponential_clock_tonelli
-- name    : AvramDividend.Classical.chat04_unbounded_killed_scale_exponential_clock_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:06:57.035564+00:00
-- url     : https://prove2.me/theorems/bed3b85f-4c39-48b9-91e5-4528b2465ea5
-- title:
--   Exact exponential-clock representation of the genuine lower-killed discounted q-scale resolvent
-- statement:
--   For any genuine unbounded-variation spectrally negative Levy process, q>0, positive independent exponential clock rate p and any initial reserve x, the product-space expectation of the discounted q-scale payoff observed before the strict lower exit equals the time integral of the actual killed expected payoff weighted by the exponential density. The survival event and reward are proved measurable from the genuine process and scale function; no killed harmonicity, spatial resolvent kernel or two-sided exit identity is assumed.
-- source:
--   Independent stochastic resolvent/time-integral construction via actual process measurability (d55462c3), strict lower killing event (c740e195), and exponential clock Tonelli (846f9b05). Scale continuity from c1b8958a and 9e68affb. Non-circular bridge prior to Wiener-Hopf identification of spatial killed resolvent kernel.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Mathlib.Probability.Distributions.Exponential

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_scale_exponential_clock_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q p : ℝ) (hq : 0 < q) (hp : 0 < p)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator
        (fun z => ENNReal.ofReal
          (Real.exp (-q * z.2) * W (x + X.X (Real.toNNReal z.2) z.1))) z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
      (∫⁻ ω : Ω,
        ({z : Ω × ℝ | 0 ≤ z.2 ∧
          ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator
          (fun z => ENNReal.ofReal
            (Real.exp (-q * z.2) * W (x + X.X (Real.toNNReal z.2) z.1)))
          (ω, t) ∂P) ∂volume) := by sorry
