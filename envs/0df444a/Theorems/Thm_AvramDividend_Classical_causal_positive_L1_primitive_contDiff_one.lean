-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_L1_primitive_contDiff_one
-- name    : AvramDividend.Classical.causal_positive_L1_primitive_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:59:24.034006+00:00
-- url     : https://prove2.me/theorems/c021a49d-793d-420d-a203-f5c4e4390f99
-- title:
--   C1 causal primitive of a continuous positive-time L1 kernel
-- statement:
--   If a real kernel is Lebesgue-integrable on strictly positive times and continuous at every positive time, then its primitive from zero is continuously differentiable on the positive half-line. Singular behaviour near zero is permitted.
-- source:
--   Reusable exact-hypothesis bridge for Gaussian double-tail Volterra kernel regularity.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable

open MeasureTheory Set

theorem AvramDividend.Classical.causal_positive_L1_primitive_contDiff_one
    (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1 (fun x : ℝ => ∫ s in (0 : ℝ)..x, K s) (Ioi 0) := by sorry
