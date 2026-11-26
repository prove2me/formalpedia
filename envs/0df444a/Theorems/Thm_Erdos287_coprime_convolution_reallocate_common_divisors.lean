-- Prove2me | Theorems.Thm_Erdos287_coprime_convolution_reallocate_common_divisors
-- name    : Erdos287.coprime_convolution_reallocate_common_divisors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T22:03:37.979878+00:00
-- url     : https://prove2.me/theorems/04b2c7d0-85be-5743-8c1f-f119b246f92c
-- title:
--   Reallocation of common divisors in a coprime sieve convolution
-- statement:
--   A coprime convolution with factors at most R and S and arbitrary complex product weight E can be expanded over common divisors d at most min(R,S). The d term has coefficient mu(d), independent indices u at most R/d and v at most S/d, factors A(du) and B(dv), and product weight E(d^2uv).
-- source:
--   Erdős #287, upper linear sieve assembly with factorable weights.

import Mathlib

theorem Erdos287.coprime_convolution_reallocate_common_divisors (R S : ℕ) (A B E : ℕ → ℂ) :
    (∑ r ∈ Finset.Icc 1 R, ∑ s ∈ (Finset.Icc 1 S).filter (fun s => r.Coprime s),
      A r * B s * E (r * s)) =
    ∑ d ∈ Finset.Icc 1 (min R S), (ArithmeticFunction.moebius d : ℂ) *
      ∑ u ∈ Finset.Icc 1 (R / d), ∑ v ∈ Finset.Icc 1 (S / d),
        A (d * u) * B (d * v) * E (d * d * u * v) := by sorry
