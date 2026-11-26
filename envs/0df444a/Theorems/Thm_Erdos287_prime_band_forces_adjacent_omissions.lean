-- Prove2me | Theorems.Thm_Erdos287_prime_band_forces_adjacent_omissions
-- name    : Erdos287.prime_band_forces_adjacent_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:22:41.600097+00:00
-- url     : https://prove2.me/theorems/80b79ef5-258c-5e9f-b534-c9db47476f17
-- title:
--   A prime-band criterion forcing two consecutive omissions
-- statement:
--   In an exact unit-fraction representation from $[m,M]$, let $H$ be a known set of omissions in that interval. Consider a set $P$ of primes at least $Y$ with $\lfloor M/p\rfloor$ at most $B$ and at least $R$ cofactor positions in the interval. Suppose fewer than $R$ positions in each layer have no neighbor in $H$. If $B\operatorname{lcm}(1,\ldots,B)<Y^{K+1}$ and $|P|>(B+1)^2K\sum_{j<R}\binom Bj$, then there are two consecutive omissions, at least one in $H$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.prime_band_forces_adjacent_omissions (D H P : Finset ℕ) (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D) (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1))
    (hfew : ∀ p ∈ P,
      ((Finset.Icc ((m - 1) / p + 1) (M / p)).filter
        (fun c => c * p - 1 ∉ H ∧ c * p + 1 ∉ H)).card < R)
    (hmany : ((B + 1) * (B + 1)) * (∑ j ∈ Finset.range R, B.choose j) * K < P.card) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D ∧ (n ∈ H ∨ n + 1 ∈ H) := by sorry
