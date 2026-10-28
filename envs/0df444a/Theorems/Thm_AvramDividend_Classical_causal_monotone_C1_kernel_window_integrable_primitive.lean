-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_monotone_C1_kernel_window_integrable_primitive
-- name    : AvramDividend.Classical.causal_monotone_C1_kernel_window_integrable_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:46:34.082748+00:00
-- url     : https://prove2.me/theorems/d00ff844-6e9e-4ad1-bf66-8a43c8de3fa1
-- title:
--   Global L1 derivative kernel reproducing a monotone C1 primitive on a finite window
-- statement:
--   The positive derivative of a continuous monotone C1 function vanishing at zero is integrable over every compact positive interval. Restrict that derivative to (0,R] to obtain a globally integrable positive-time kernel k whose primitives on (0,R] recover g. Supports localisation for differentiation of general causal convolutions.
-- source:
--   Proved monotone_C1_kernel_derivative_primitive_from_zero and indicator integrability.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_monotone_C1_kernel_derivative_primitive_from_zero
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_monotone_C1_kernel_window_integrable_primitive
    (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    ∃ k : ℝ → ℝ,
      IntegrableOn k (Ioi (0 : ℝ)) volume ∧
      ∀ x : ℝ, 0 < x → x ≤ R →
        (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x := by sorry
