-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_convolution_integrable_of_tilted_monotone
-- name    : AvramDividend.Classical.chat04_killed_resolvent_convolution_integrable_of_tilted_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:55:28.37622+00:00
-- url     : https://prove2.me/theorems/9fbed998-6c5c-4459-880b-fca9d5a3c154
-- title:
--   Integrability of killed-scale convolution by domination from the Laplace term
-- statement:
--   When W_q and W_(q+p) are nonnegative scale-like functions, W_(q+p) vanishes below zero, and its exponential tilt is monotone on the nonnegative half-line, the convolution y↦W_q(y)W_(q+p)(x-y) is bounded by the Laplace term y↦W_q(y)e^(-theta y)W_(q+p)(x). Hence integrability of the Laplace term and measurability of the convolution imply integrability of the convolution on the positive half-line. This removes a separate integrability hypothesis from the analytic resolvent identity.
-- source:
--   Domination by the verified nonnegative full-half-line killed-resolvent kernel and Mathlib's integrable monotonicity theorem.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_full_halfline

open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_resolvent_convolution_integrable_of_tilted_monotone
    (θ : ℝ) (Wq Wqp : ℝ → ℝ)
    (hmono : MonotoneOn
      (fun z : ℝ => Real.exp (-(θ * z)) * Wqp z) (Ici (0 : ℝ)))
    (hWq_nonneg : ∀ z : ℝ, 0 ≤ z → 0 ≤ Wq z)
    (hWqp_nonneg : ∀ z : ℝ, 0 ≤ Wqp z)
    (hnegative : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 ≤ x)
    (hfirst : IntegrableOn
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x))
      (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable
      (fun y : ℝ => Wq y * Wqp (x - y))
      (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun y : ℝ => Wq y * Wqp (x - y)) (Ioi (0 : ℝ)) := by sorry
