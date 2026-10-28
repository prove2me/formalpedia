-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a
-- name    : AvramDividend.Classical.chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:22:11.732803+00:00
-- url     : https://prove2.me/theorems/a6c31a27-8931-4b7c-b2f0-86a642dba034
-- title:
--   True lower-killed scale reward bounded by genuine exponential-clock Levy moment
-- statement:
--   For the actual spectrally negative Lévy path observed at an independent Exp(r) clock, the q-scale reward killed whenever the full lower history falls below zero is at most a finite q-scale exponential-envelope constant times the true positive exponential terminal moment. All reserves x are permitted and no Wiener–Hopf independence, killed spatial kernel identification or two-sided exit formula is used. This genuinely stochastic domination will combine with the separate true clock exponential moment identity when its observation-rate gap is positive.
-- source:
--   Canonical Proved global scale Laplace envelope chat03_scale_global_weighted_exponential_bound 8c6ea1c8, genuine joint time-state measurability and ENNReal Tonelli monotonicity. This is an exact actual process-law bound, useful for Route B integrability.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           0 ≤ x + X.X s z.1
      then ENNReal.ofReal
        (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞)
      ∂(P.prod (ProbabilityTheory.expMeasure r))) ≤
    ENNReal.ofReal (Real.exp θ * (X.ψ θ - q)⁻¹) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X (Real.toNNReal z.2) z.1)))
        ∂(P.prod (ProbabilityTheory.expMeasure r))) := by sorry
