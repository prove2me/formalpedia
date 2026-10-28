-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:42:36.847738+00:00
-- url     : https://prove2.me/theorems/d1036279-0261-4abd-ae04-b6386068d53a
-- title:
--   Exact genuine random-terminal Esscher stopped-clock full-path reward change-of-variables
-- statement:
--   At any measurable stopping age, the true random-terminal joint Esscher density on the original Levy path and independent real Exp(p) clock transforms stopped-history weights and complete shifted-path rewards into the exact exponentially discounted stopped-prefix likelihood times the integrated residual-clock compensated future-path likelihood. The pathwise stopped terminal-likelihood split is stated explicitly as an algebraic premise and can be discharged by the already-Proved random-clock density split. This establishes the measure-theoretic change of variables required before proving weighted Qp regeneration; it does not assume independence under Qp.
-- source:
--   Proved actual random-age exponential-clock reward shift 51ea1a74, Proved stopped terminal Esscher density split b2a39955, pinned lintegral_withDensity_eq_lintegral_mul, and exact Qp=(P.prod expMeasure p).withDensity Z_e. Both observation reward and stopped reward are assumed jointly measurable, with no future-path independence hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_exp_clock_random_age_joint_reward_shift_ws01d

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (W : Ω → ℝ≥0∞)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hObserve : Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hReward : Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp
        (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
        H (Real.toNNReal z.2)
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1))))
    (hSplit : ∀ (ω : Ω) (t : ℝ), (τ ω : ℝ) ≤ t →
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) *
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω -
          X.X (τ ω) ω) -
          (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ))) :
    (∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then
        W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1)
      else 0
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
      (∫⁻ u : ℝ,
        (W ω * ENNReal.ofReal (Real.exp
          (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ))) *
        (ENNReal.ofReal (Real.exp
          (θ * (X.X (τ ω + Real.toNNReal u) ω - X.X (τ ω) ω) -
            (Real.toNNReal u : ℝ) * X.ψ θ)) *
          H (Real.toNNReal u)
            (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω))
        ∂(expMeasure p)) ∂P) := by sorry
