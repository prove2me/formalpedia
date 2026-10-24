-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_deriv_eq_continuous_positive
-- name    : AvramDividend.Classical.causal_l1_primitive_deriv_eq_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:42:46.469896+00:00
-- url     : https://prove2.me/theorems/307887c8-e2d3-4f52-9b50-ddd3dc9a561b
-- title:
--   Derivative of a causal L1 primitive with positive-time continuity
-- statement:
--   An integrable causal kernel that is continuous on the positive axis has a causal primitive with derivative equal to the kernel at every strictly positive time, including when the kernel is unbounded or discontinuous at zero. Supports termwise differentiability of Volterra convolution powers.
-- source:
--   Fundamental theorem of calculus for interval integrals, Mathlib intervalIntegral.integral_hasDerivAt_right.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Topology

namespace AvramDividend.Classical

theorem causal_l1_primitive_deriv_eq_continuous_positive
    (g : ℝ → ℝ)
    (hgInt : IntegrableOn g (Ioi (0 : ℝ)) volume)
    (hgCont : ContinuousOn g (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, g s ∂volume) x = g x := by sorry

end AvramDividend.Classical
