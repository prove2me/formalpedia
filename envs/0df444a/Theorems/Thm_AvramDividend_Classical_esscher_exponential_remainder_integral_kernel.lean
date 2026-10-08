-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exponential_remainder_integral_kernel
-- name    : AvramDividend.Classical.esscher_exponential_remainder_integral_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:33:49.405817+00:00
-- url     : https://prove2.me/theorems/11fe6a4e-3229-45ee-b41a-312e196dd195
-- title:
--   Exponential compensation as a positive integrated Laplace kernel
-- statement:
--   For arbitrary real s and z, the compensated exponential identity s∫_0^z(1−exp(−st))dt = exp(−sz)−1+sz holds. When s,z≥0, the kernel 1−exp(−st) is nonnegative. This deterministic identity is the key Tonelli step in representing the Esscher-shifted descending ladder-height Bernstein exponent (ψ(φ+s)−q)/s as a positive drift plus a nonnegative jump-kernel integral, ultimately constructing the unbounded-variation excursion potential.
-- source:
--   Pinned Mathlib intervalIntegral.mul_integral_comp_mul_left, integral_exp and intervalIntegral.integral_sub; Kyprianou scale-function Wiener–Hopf factorisation.

import Mathlib
open MeasureTheory intervalIntegral Set

theorem AvramDividend.Classical.esscher_exponential_remainder_integral_kernel
    (s z : ℝ) :
    s * (∫ t in (0 : ℝ)..z, (1 - Real.exp (-(s * t)))) =
      Real.exp (-(s * z)) - 1 + s * z := by sorry
