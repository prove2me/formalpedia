-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_head_step
-- name    : AvramDividend.Classical.causal_neumann_gaussian_head_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:00:52.475702+00:00
-- url     : https://prove2.me/theorems/0a614f21-3589-46bb-bbf9-0077f47c5ba3
-- title:
--   Initial Gaussian Neumann correction satisfies the exact Volterra recurrence
-- statement:
--   The first normalised correction to the Gaussian derivative-resolvent series is exactly the negative causal convolution of the full kernel with the constant initial term, divided by a. This is the base case of the recurrence required to establish the complete resolvent identity.
-- source:
--   The Proved initial weighted primitive identity states the first correction as -a⁻¹ times the kernel integral. The Proved positive_Ioc_causal_convolution_comm_real reflects the integration variable, and scalar extraction identifies the constant first term Q0=1/a. Together they supply the n=0 case of hstep in causal_neumann_resolvent_dominated_convergence.

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_gaussian_initial_weighted_primitive
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_gaussian_head_step
    (a w β : ℝ) (K k : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQ1 : Q 1 = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * k t ∂volume)) :
    ∀ x : ℝ, 0 < x →
      Q 1 x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * Q 0 s ∂volume) := by sorry
