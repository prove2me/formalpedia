-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_signed_damped_kernel_data
-- name    : AvramDividend.Classical.causal_gaussian_signed_damped_kernel_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:47:50.048005+00:00
-- url     : https://prove2.me/theorems/a1d56909-f5e0-4333-9572-19fd9d9eb909
-- title:
--   Causal measurable signed Gaussian kernel from its positive integrable envelope
-- statement:
--   Given a positive Gaussian Volterra coefficient, a continuous positive-time real kernel and an integrable exponentially damped positive envelope, construct the negative signed causal kernel. The kernel is positive-time integrable and continuous, globally measurable, zero on nonpositive time and pointwise dominated by the positive envelope.
-- source:
--   Causal zero-extension and positive-time continuity imply measurability; the signed kernel is dominated by its positive envelope, yielding L1 integrability by Integrable.mono'. This supplies the k hypotheses of causal_neumann_C1_from_antitone_envelope_powers.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_continuous_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_causal_signed_weighted_kernel_abs_le_envelope

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_signed_damped_kernel_data
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a)
    (hKcont : ContinuousOn K (Ioi (0 : ℝ)))
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t)
    (hEnvelope : IntegrableOn
      (fun t : ℝ => a⁻¹ * Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume) :
    ∃ k : ℝ → ℝ,
      k = (fun t : ℝ =>
        if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0) ∧
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      Measurable k ∧
      ContinuousOn k (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → k t = 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        |k t| ≤ a⁻¹ * Real.exp (-w * t) * (|β| + K t)) := by sorry
