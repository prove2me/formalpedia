-- Prove2me | Theorems.Thm_Erdos287_prime_power_cofactor_log_bound
-- name    : Erdos287.prime_power_cofactor_log_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:04:49.21042+00:00
-- url     : https://prove2.me/theorems/93ae6700-287e-4720-838c-65d38929ea0b
-- title:
--   A logarithmic bound for prime-power divisors of a denominator
-- statement:
--   Let $1<n_0<\cdots<n_{k-1}=M$ have reciprocal sum one and $k\ge2$. If a prime power $p^a$, with $a\ge1$, divides any denominator, set $B=\lfloor M/p^a\rfloor$. Then $\log p\le\log B+\psi(B)$, where $\psi$ is Chebyshev's second function.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Uses the cofactor exclusion and the identity between Chebyshev psi and the logarithm of the LCM. The lower-bound application uses the joint Dickman law, Theorem 1.1, https://github.com/openai/math/blob/main/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf.

import Mathlib

theorem Erdos287.prime_power_cofactor_log_bound (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p e i : ℕ) (hp : Nat.Prime p) (he : 1 ≤ e) (hi : i < k) (hd : p ^ e ∣ f i) :
    let B := f (k - 1) / p ^ e
    Real.log p ≤ Real.log B + Chebyshev.psi B := by sorry
