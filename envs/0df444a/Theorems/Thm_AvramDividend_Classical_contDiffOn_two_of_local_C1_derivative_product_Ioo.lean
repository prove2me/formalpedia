-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_local_C1_derivative_product_Ioo
-- name    : AvramDividend.Classical.contDiffOn_two_of_local_C1_derivative_product_Ioo
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:08:16.110879+00:00
-- url     : https://prove2.me/theorems/cbf37b14-936e-4c84-82f1-4dd9b2ca6277
-- title:
--   Local C2 regularity from a C1 logarithmic derivative on an open interval
-- statement:
--   If W is continuous, g is C1, and W'=Wg pointwise on an open real interval, then W is C2 on that interval. The interval-local conclusion permits patching C1 resolvent results established separately on compact positive-time windows.
-- source:
--   Interval-local analogue of the proved positive-half-line product derivative bridge for Gaussian Neumann resolvent regularity.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set

theorem AvramDividend.Classical.contDiffOn_two_of_local_C1_derivative_product_Ioo
    (W g : ℝ → ℝ) (a b : ℝ)
    (hW : ContinuousOn W (Ioo a b))
    (hg : ContDiffOn ℝ 1 g (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt W (W x * g x) x) :
    ContDiffOn ℝ 2 W (Ioo a b) := by sorry
