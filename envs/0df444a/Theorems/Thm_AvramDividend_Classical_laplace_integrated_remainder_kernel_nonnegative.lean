-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_integrated_remainder_kernel_nonnegative
-- name    : AvramDividend.Classical.laplace_integrated_remainder_kernel_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:35:27.728703+00:00
-- url     : https://prove2.me/theorems/97a0b5a3-659c-4e94-b50c-6e85903491f8
-- title:
--   Positivity of the integrated Laplace exponential remainder kernel
-- statement:
--   The elementary Laplace kernel 1−exp(−s t) is nonnegative for all s,t≥0. Together with the integrated exponential compensation identity, this supplies the positivity required to construct a Bernstein/ladder-height jump kernel from the Esscher-shifted Lévy–Khintchine exponent.
-- source:
--   Pinned Mathlib Real.exp_le_one_iff; source-neutral positive Laplace kernel.

import Mathlib

theorem AvramDividend.Classical.laplace_integrated_remainder_kernel_nonnegative
 (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
 0 ≤ 1 - Real.exp (-(s * t)) := by sorry
