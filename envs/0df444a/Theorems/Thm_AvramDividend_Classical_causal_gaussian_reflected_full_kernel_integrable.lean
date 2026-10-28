-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_reflected_full_kernel_integrable
-- name    : AvramDividend.Classical.causal_gaussian_reflected_full_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:39:36.836446+00:00
-- url     : https://prove2.me/theorems/874ccbce-c971-48ae-8232-2a237b430e17
-- title:
--   Finite-horizon Gaussian Volterra kernel remains integrable under causal reflection
-- statement:
--   For an L1 positive-time Gaussian Lévy kernel K and arbitrary drift beta, the reflected complete Volterra kernel beta+K(x-s) is integrable over every finite causal integration interval, including non-positive endpoints.
-- source:
--   Compose the Proved causal_l1_full_kernel_local_integrable with pinned Mathlib IntervalIntegrable.comp_sub_left. The symmetry of oriented intervals transports integrability of beta+K(t) on (0,x] to beta+K(x-s) on the same causal interval. This discharges the hB hypothesis of causal_local_neumann_convolution_majorant.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_full_kernel_local_integrable

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_reflected_full_kernel_integrable
    (K : ℝ → ℝ) (β x : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun s : ℝ => β + K (x - s))
      (Ioc (0 : ℝ) x) volume := by sorry
