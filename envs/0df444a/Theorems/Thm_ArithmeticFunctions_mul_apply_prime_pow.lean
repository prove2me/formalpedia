-- Prove2me | Theorems.Thm_ArithmeticFunctions_mul_apply_prime_pow
-- name    : ArithmeticFunctions.mul_apply_prime_pow
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:12:03.908955+00:00
-- url     : https://prove2.me/theorems/a24781f5-8303-4cc1-b9ce-0ddfcef2ebd0
-- title:
--   Dirichlet convolution evaluated at a prime power
-- statement:
--   **The Dirichlet convolution at a prime power is a finite convolution of exponents.**
--
--   For arithmetic functions $f, g$ and a prime $p$,
--
--   $$(f * g)(p^{k}) \;=\; \sum_{i=0}^{k} f(p^{i})\,g(p^{k-i}).$$
--
--   In general $(f*g)(n) = \sum_{d \mid n} f(d)g(n/d)$, a sum over the divisors of $n$. At a prime
--   power the divisors are exactly $1, p, p^{2}, \dots, p^{k}$, each occurring once, so the divisor
--   sum collapses into a sum over the exponent $i \in \{0,\dots,k\}$ — an ordinary Cauchy product
--   of the sequences $(f(p^i))_i$ and $(g(p^i))_i$.
--
--   This is the computational heart of why multiplicative functions are determined by their values
--   on prime powers, and why the Euler product of a Dirichlet series factors: the local factor at
--   $p$ of $f * g$ is the product of the local factors of $f$ and of $g$. Every explicit evaluation
--   of a convolution — $\mu * 1 = \delta$, $\Lambda * 1 = \log$, $\sigma = \mathrm{id} * 1$ — is
--   verified through this identity at each prime separately.
--
--   **Formalization note.** `ArithmeticFunction` multiplication is Dirichlet convolution; the
--   index runs over `Finset.range (k+1)`, i.e. $0 \le i \le k$, and $k - i$ is natural
--   subtraction, which is exact here since $i \le k$.
-- source:
--   Classical; see Apostol, *Introduction to Analytic Number Theory*, §2.6, and Montgomery & Vaughan, *Multiplicative Number Theory I*, §1.2. Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ArithmeticFunctions

open ArithmeticFunction in
theorem mul_apply_prime_pow {f g : ArithmeticFunction ℂ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by sorry

end ArithmeticFunctions
