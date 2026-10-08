-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_two_linear_remainder_isBigO
-- name    : AvramDividend.Classical.contDiffOn_two_linear_remainder_isBigO
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T11:37:38.717545+00:00
-- url     : https://prove2.me/theorems/f6c8b92a-97fa-4f79-b8c4-4e832f718f84
-- title:
--   A C2 function has quadratic first-order Taylor remainder locally
-- statement:
--   Pure calculus helper. If f is C2 on an open interval containing x, then its first-order Taylor remainder at x is O(y^2) as y tends to zero: f(x+y)-f(x)-f'(x)y = O(y^2). The proof uses Mathlib's Taylor theorem on the open interval, identifies the degree-two Taylor polynomial at the interior point with f(x)+f'(x)y+(f''(x)/2)y^2, and absorbs the quadratic term into the little-o Taylor remainder.
-- source:
--   Standard second-order Taylor expansion; formalized using Mathlib.Analysis.Calculus.Taylor.

import Mathlib

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.contDiffOn_two_linear_remainder_isBigO
    (f : ℝ → ℝ) (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    (fun y : ℝ => f (x + y) - f x - deriv f x * y) =O[𝓝 0]
      (fun y : ℝ => y ^ 2) := by sorry
