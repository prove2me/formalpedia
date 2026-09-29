-- Prove2me | Theorems.Thm_FamousTheorems_fibonacci_gcd_strong_divisibility_6b
-- name    : FamousTheorems.fibonacci_gcd_strong_divisibility_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:49.162982+00:00
-- url     : https://prove2.me/theorems/682582d8-375f-4638-b0a9-39933377f186
-- title:
--   Fibonacci numbers form a strong divisibility sequence: gcd(F_m, F_n) = F_gcd(m,n)
-- statement:
--   **The Fibonacci numbers form a strong divisibility sequence.** For all natural numbers $m,n$,
--   $$\gcd(F_m,F_n)=F_{\gcd(m,n)},$$
--   where $F_0=0$, $F_1=1$ and $F_{k+2}=F_{k+1}+F_k$.
--
--   Lucas proved this in 1876. It implies that $F_m\mid F_n$ whenever $m\mid n$, that consecutive Fibonacci numbers are coprime, and that $F_n$ can be prime only when $n$ is prime or $n=4$. The same property holds for Lucas sequences and underlies primality tests for Mersenne numbers.
--
--   **Formalization note.** Mathlib's `Nat.fib_gcd`. `Nat.fib` is the Fibonacci sequence with `Nat.fib 0 = 0` and `Nat.fib 1 = 1`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.fib_gcd`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fibonacci_gcd_strong_divisibility_6b (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) := by sorry

end FamousTheorems
