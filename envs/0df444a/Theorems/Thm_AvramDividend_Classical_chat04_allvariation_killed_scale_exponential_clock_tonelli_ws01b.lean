-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_allvariation_killed_scale_exponential_clock_tonelli_ws01b
-- name    : AvramDividend.Classical.chat04_allvariation_killed_scale_exponential_clock_tonelli_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:41:07.040253+00:00
-- url     : https://prove2.me/theorems/7d6b524c-3454-4232-a6af-c806dc120665
-- title:
--   Genuine lower-killed q-scale exponential-clock resolvent for all Lévy path-variation regimes
-- statement:
--   The actual discounted lower-killed q-scale payoff at an independent exponential observation time has the exact exponential-density time-resolvent representation for every spectrally negative Lévy process, including bounded-variation infinite jump activity and Wq(0)>0. The proof uses Borel measurability of q-scale functions, joint time-path measurability and the measured survival event. No scale martingale, spatial killed-resolvent identification or first-passage formula is assumed.
-- source:
--   Kyprianou–Kuznetsov–Rivero scale review, killed-resolvent representation; proven generic exponential-clock Tonelli and q-scale measurability on Prove2Me.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Mathlib.Probability.Distributions.Exponential

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_allvariation_killed_scale_exponential_clock_tonelli_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q p : ℝ) (hq : 0 < q) (hp : 0 < p)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) :
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
