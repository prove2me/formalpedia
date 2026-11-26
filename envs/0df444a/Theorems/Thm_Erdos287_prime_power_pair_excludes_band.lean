-- Prove2me | Theorems.Thm_Erdos287_prime_power_pair_excludes_band
-- name    : Erdos287.prime_power_pair_excludes_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T02:50:16.73314+00:00
-- url     : https://prove2.me/theorems/80b23ae7-f6be-479f-bb15-dc7e985c9970
-- title:
--   Consecutive prime-power certificates exclude a band of largest denominators
-- statement:
--   Suppose $1=f(0)^{-1}+\cdots+f(k-1)^{-1}$ with $1<f(0)<\cdots<f(k-1)=M$ and $k\ge2$. Fix $x>0$ with $x+1\le M<\mathrm e x$. Suppose $p^a\mid x$ and $q^b\mid x+1$ for primes $p,q$ and positive exponents $a,b$. For $s\ge0$ write $L_s=\operatorname{lcm}(1,\ldots,s)$. Assume there are bounds $B<p$ and $D<q$ with
--
--   $$
--   M<(B+1)p^a,\quad M<(D+1)q^b,\quad
--   \sum_{c=1}^{B}L_B/c<p,\quad \sum_{c=1}^{D}L_D/c<q.
--   $$
--
--   Then at least one pair of consecutive denominators has difference at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. For unbounded pairs with large prime factors see Kevin Ford and James Maynard, Theorem 7.19 in https://ford126.web.illinois.edu/sieve2023.pdf.

import Mathlib

theorem Erdos287.prime_power_pair_excludes_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (x : ℕ) (hx : 0 < x) (hlo : x + 1 ≤ f (k - 1))
    (hhi : (f (k - 1) : ℝ) < Real.exp 1 * x)
    (p q e d B D : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hdivp : p ^ e ∣ x) (hdivq : q ^ d ∣ x + 1) (hB : B < p) (hD : D < q)
    (hmaxp : f (k - 1) < (B + 1) * p ^ e) (hmaxq : f (k - 1) < (D + 1) * q ^ d)
    (hsmallp : (∑ j ∈ Finset.Icc 1 B, Nat.lcmUpto B / j) < p)
    (hsmallq : (∑ j ∈ Finset.Icc 1 D, Nat.lcmUpto D / j) < q) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
