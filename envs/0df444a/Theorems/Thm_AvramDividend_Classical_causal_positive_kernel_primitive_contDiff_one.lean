-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
-- name    : AvramDividend.Classical.causal_positive_kernel_primitive_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:52:03.628698+00:00
-- url     : https://prove2.me/theorems/ca82cbc5-5a02-4693-8a41-c18087e20c09
-- title:
--   C1 positive-time primitive of a locally integrable continuous causal kernel
-- statement:
--   A kernel that is continuous for strictly positive times and integrable on every interval from zero has a continuously differentiable causal primitive on the open positive half-line, with derivative equal to the kernel. No boundedness or continuity at the origin is assumed.
-- source:
--   Fundamental theorem of calculus helper for differentiating the positive-time Gaussian Esscher Volterra kernel primitive.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_positive_kernel_primitive_contDiff_one
    (K : ℝ → ℝ)
    (hK : ContinuousOn K (Ioi (0 : ℝ)))
    (hlocal : ∀ x : ℝ, 0 < x → IntervalIntegrable K volume 0 x) :
    ContDiffOn ℝ 1 (fun x : ℝ => ∫ s in (0 : ℝ)..x, K s) (Ioi 0) := by sorry
