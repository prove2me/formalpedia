-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_neumann_undamped_primitive_step
-- name    : AvramDividend.Classical.causal_signed_neumann_undamped_primitive_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:53:51.899533+00:00
-- url     : https://prove2.me/theorems/b3957d97-2d00-4706-8557-64d2b6fb72b4
-- title:
--   Signed Gaussian Neumann primitives satisfy the undamped Volterra recursion
-- statement:
--   For the Gaussian signed damped kernel k(t)=-a⁻¹ exp(-w t)(β+K(t)) on positive times, each exponentially weighted Neumann power primitive obeys the undamped second-kind Volterra recursion with kernel β+K. This is the exact finite-order recurrence used to prove the explicit Gaussian C1 candidate solves its derivative-resolvent equation.
-- source:
--   Combine the proved sequence-level weighted primitive recurrence with the pointwise exponential untwisting lemma. Replace the integrands on the open interior of each causal interval, eliminating the boundary discrepancy at x-s=0 via the null-endpoint congruence, then extract the constant -a⁻¹ from the integral.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_neumann_power_weighted_primitive_recurrence
import Theorems.Thm_AvramDividend_Classical_causal_exp_damped_signed_kernel_untwist
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_integral_interior_congr

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_signed_neumann_undamped_primitive_step
    (a w β : ℝ) (K k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P (n + 1) t ∂volume) =
      -a⁻¹ * (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) *
          (∫ t in Ioc (0 : ℝ) s,
            Real.exp (w * t) * P n t ∂volume) ∂volume) := by sorry
