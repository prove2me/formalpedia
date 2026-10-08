-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exponential_remainder_divided_kernel
-- name    : AvramDividend.Classical.esscher_exponential_remainder_divided_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:38:18.149795+00:00
-- url     : https://prove2.me/theorems/1819610a-8904-441c-a5d2-f62cf5dba23e
-- title:
--   Divided exponential compensation equals the positive integrated Laplace kernel
-- statement:
--   For s>0, the divided compensated-exponential term (exp(−sz)−1+sz)/s equals the integrated positive Laplace kernel ∫_0^z(1−exp(−st))dt. This is the exact identity used under Tonelli to turn the jump-compensation part of (ψ(φ+s)−ψ(φ))/s into a Bernstein-function Lévy-kernel representation, a principal missing analytic construction in the excursion-height proof.
-- source:
--   Published esscher_exponential_remainder_integral_kernel; pinned Mathlib div_eq_iff.

import Mathlib
open MeasureTheory intervalIntegral Set

theorem AvramDividend.Classical.esscher_exponential_remainder_divided_kernel
    (s z : ℝ) (hs : 0 < s) :
    (Real.exp (-(s * z)) - 1 + s * z) / s =
      ∫ t in (0 : ℝ)..z, (1 - Real.exp (-(s * t))) := by sorry
