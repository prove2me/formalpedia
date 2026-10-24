-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_full_kernel_convolution_continuousOn_nonnegative
-- name    : AvramDividend.Classical.causal_full_kernel_convolution_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:22:25.185766+00:00
-- url     : https://prove2.me/theorems/4e7ac4c2-349c-4be5-ae8d-201cafc00ac6
-- title:
--   The drift-plus-L1 Volterra convolution preserves nonnegative-time continuity
-- statement:
--   For a constant β, an L1 causal kernel K and an input V continuous and locally bounded on nonnegative times, the complete causal convolution x↦∫_(0,x](β+K(x−s))V(s)ds is continuous on [0,∞), including at zero. Split the integral into β times the continuous primitive of V and the L1 convolution, which is now Proved continuous through time zero. Verify integrability of each summand before applying Bochner integral linearity. This is the analytic mapping-continuity input to the weighted Banach fixed-point construction.

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_full_kernel_convolution_continuousOn_nonnegative
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ici (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume)
      (Ici (0 : ℝ)) := by sorry
