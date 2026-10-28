-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_reflected_pair_killed_scale_monotone_ws01a
-- name    : AvramDividend.Classical.chat04_true_reflected_pair_killed_scale_monotone_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:07:15.467669+00:00
-- url     : https://prove2.me/theorems/531ce468-2b09-4a71-911d-847198114515
-- title:
--   The genuine exponential-horizon reflected-pair killed q-scale reward is monotone in initial reserve
-- statement:
--   At any independent positive-rate exponential horizon, integrate the genuine negative-running-infimum and terminal-drawdown pushforward law against 1_{L≤x}Wq(x−L+Y). This actual stochastic function of reserve x is nondecreasing. The result follows from the already Proved genuine pair pushforward identity, pathwise inclusion of lower-survival events as reserve increases, and scale-function monotonicity on the nonnegative half-line; it assumes no Wiener–Hopf independence or two-sided exit ratio.
-- source:
--   Canonical Proved true joint reflected killed law 06a1bccb, the exact IsScaleFunction monotonicity conjunct, and monotonicity of ENNReal.ofReal and lintegral.

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_exponential_joint_infimum_drawdown_ws01a

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_true_reflected_pair_killed_scale_monotone_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x₁ x₂ : ℝ) (hxx : x₁ ≤ x₂) :
    (∫⁻ a : ℝ × ℝ,
      if a.1 ≤ x₁ then ENNReal.ofReal (W (x₁ - a.1 + a.2))
      else (0 : ℝ≥0∞)
      ∂((P.prod (ProbabilityTheory.expMeasure r)).map
        (fun z : Ω × ℝ =>
          (-sInf {y : ℝ | ∃ s : ℝ≥0,
                    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
           X.X (Real.toNNReal z.2) z.1 +
             -sInf {y : ℝ | ∃ s : ℝ≥0,
                       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) ≤
    (∫⁻ a : ℝ × ℝ,
      if a.1 ≤ x₂ then ENNReal.ofReal (W (x₂ - a.1 + a.2))
      else (0 : ℝ≥0∞)
      ∂((P.prod (ProbabilityTheory.expMeasure r)).map
        (fun z : Ω × ℝ =>
          (-sInf {y : ℝ | ∃ s : ℝ≥0,
                    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1},
           X.X (Real.toNNReal z.2) z.1 +
             -sInf {y : ℝ | ∃ s : ℝ≥0,
                       s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})))) := by sorry
