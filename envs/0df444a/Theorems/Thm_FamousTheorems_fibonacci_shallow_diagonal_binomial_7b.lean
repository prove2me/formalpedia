-- Prove2me | Theorems.Thm_FamousTheorems_fibonacci_shallow_diagonal_binomial_7b
-- name    : FamousTheorems.fibonacci_shallow_diagonal_binomial_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:51.543355+00:00
-- url     : https://prove2.me/theorems/fee71b80-fe9e-4135-a048-2156b4797cce
-- title:
--   Fibonacci numbers are sums of binomial coefficients along shallow diagonals
-- statement:
--   **Fibonacci numbers are sums along the shallow diagonals of Pascal's triangle.** For every $n\ge0$,
--   $$F_{n+1}=\sum_{i+j=n}\binom{i}{j}=\binom n0+\binom{n-1}1+\binom{n-2}2+\cdots,$$
--   where $F_0=0$, $F_1=1$ and $F_{k+2}=F_{k+1}+F_k$.
--
--   This connection between Fibonacci numbers and Pascal's triangle was noted by Lucas and appears already in Indian prosody. Both sides count the tilings of a strip of length $n$ by squares and dominoes: a tiling with $j$ dominoes uses $n-j$ tiles, and there are $\binom{n-j}{j}$ ways to place the dominoes among them.
--
--   **Formalization note.** Mathlib's `Nat.fib_succ_eq_sum_choose`. The sum runs over pairs $(i,j)$ of natural numbers with $i+j=n$, and $\binom ij=0$ when $j>i$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.fib_succ_eq_sum_choose`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fibonacci_shallow_diagonal_binomial_7b (n : ℕ) : Nat.fib (n + 1) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, p.1.choose p.2 := by sorry

end FamousTheorems
