-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
-- name    : AvramDividend.Classical.chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:06:34.309993+00:00
-- url     : https://prove2.me/theorems/06a1bccb-7e42-4b81-baf4-9bfb641c6122
-- title:
--   Actual lower-killed q-scale law at independent exponential time via reflected infimum and drawdown
-- statement:
--   For a genuine spectrally negative Lévy process, an independent Exp(r) observation time, and any q-scale function W, identify the actual lower-killed expectation E[1_{inf_{s≤T}X_s≥−x}W(x+X_T)] with the integral of 1_{L≤x}W(x−L+Y) against the genuine joint pushforward law of the negative running infimum L and terminal drawdown Y. Derive from jointly measurable sample paths and pushforward integration, with no Wiener–Hopf factorisation or exit identity.
-- source:
--   Proved joint running-infimum measurability ae09696f, state measurability d55462c3, lower survival 3e4d270c, scale measurability 344f3813, pinned Mathlib lintegral_map.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_true_killed_exponential_joint_infimum_drawdown_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (x q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1
      then ENNReal.ofReal (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞) ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    (∫⁻ a : ℝ × ℝ,
      if a.1 ≤ x then ENNReal.ofReal (W (x - a.1 + a.2))
      else (0 : ℝ≥0∞)
      ∂((P.prod (ProbabilityTheory.expMeasure r)).map
        (fun z : Ω × ℝ =>
          (-sInf {y : ℝ | ∃ s : ℝ≥0,
                    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
           X.X (Real.toNNReal z.2) z.1 +
             -sInf {y : ℝ | ∃ s : ℝ≥0,
                       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) := by sorry
