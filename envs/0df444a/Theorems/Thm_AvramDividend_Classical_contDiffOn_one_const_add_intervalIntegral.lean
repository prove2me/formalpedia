-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
-- name    : AvramDividend.Classical.contDiffOn_one_const_add_intervalIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:23:22.82752+00:00
-- url     : https://prove2.me/theorems/4556a986-d624-4383-a570-93e649b9d8fb
-- title:
--   A cumulative integral of a continuous density is C1 on the positive half-line
-- statement:
--   If a real density f is continuous on (0,infinity) and interval-integrable from 0 to each positive x, then its cumulative primitive G(x)=c+integral_0^x f is continuously differentiable on (0,infinity). Its derivative there is f. This isolates the calculus endpoint of the bounded-variation absolutely-continuous Lévy renewal-density argument.
-- source:
--   Pinned Mathlib intervalIntegral.integral_hasDerivAt_right, uniqueDiffOn_Ioi, contDiffOn_one_iff_derivWithin and derivWithin_of_isOpen.

import Mathlib
open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.contDiffOn_one_const_add_intervalIntegral
    (f : ℝ → ℝ) (c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) :
    ContDiffOn ℝ 1 (fun x : ℝ => c + ∫ y in (0 : ℝ)..x, f y) (Ioi 0) := by sorry
