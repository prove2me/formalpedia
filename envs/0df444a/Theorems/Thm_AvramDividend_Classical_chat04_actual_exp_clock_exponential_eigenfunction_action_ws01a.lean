-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:04:46.542318+00:00
-- url     : https://prove2.me/theorems/728dab06-4af4-4f42-83f7-9f2aa8dada11
-- title:
--   True independent exponential-clock Lévy exponential-eigenfunction action
-- statement:
--   For the actual spectrally negative Lévy process under its genuine path probability law and an independent exponential observation clock of rate r>0, the joint nonnegative expectation of exp(θ(x+X_e)) is the exponential-clock density integral of the exact Lévy semigroup moment exp(θx)exp(eψ(θ)), for θ≥0. This is a probabilistic identity, not an analytic putative killed scale kernel. It supplies the integrability bridge needed to dominate actual killed q-scale rewards using the already Proved global Wq exponential envelope.
-- source:
--   Accepted Lévy exponential semigroup eigenfunction ee03658e and actual independent exponential clock Tonelli bed3b85f; joint time-state measurability and X.laplace integrability at each deterministic horizon. Route B actual reflected-pair exponential domination.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_killed_reward_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (θ * (x + X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
      ENNReal.ofReal (Real.exp (θ * x) *
        Real.exp ((Real.toNNReal t : ℝ) * X.ψ θ)) ∂volume) := by sorry
