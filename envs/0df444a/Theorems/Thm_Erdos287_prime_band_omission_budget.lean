-- Prove2me | Theorems.Thm_Erdos287_prime_band_omission_budget
-- name    : Erdos287.prime_band_omission_budget
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:21:44.151252+00:00
-- url     : https://prove2.me/theorems/925a15ac-e99a-483f-83f8-618e285984a2
-- title:
--   A reciprocal sum budget for omissions below a full-layer cutoff
-- statement:
--   Let $D\subseteq[m,M]$ have reciprocal sum one, and let $H$ be a set of already established omissions within $[m,M]$. Let $P$ consist of primes at least $Y$, with $M<Y^2$, whose layers have at least $R$ cofactor positions and $\lfloor M/p\rfloor\le B$. Assume no member of $H$ is divisible by a prime in $P$. Set $L=\operatorname{lcm}(1,\ldots,B)$ and suppose $BL<Y^{K+1}$. With $E=(B+1)^2K\sum_{j<R}\binom Bj$, the full interval has reciprocal mass at least $1+\sum_{n\in H}1/n+R\max(0,|P|-E)/M$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.prime_band_omission_budget (D H P : Finset ℕ) (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D)
    (hYM : M < Y ^ 2) (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hsep : ∀ p ∈ P, ∀ n ∈ H, ¬ p ∣ n)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1)) :
    let E := ((B + 1) * (B + 1)) * (∑ j ∈ Finset.range R, B.choose j) * K
    1 + (∑ n ∈ H, (1 : ℚ) / n) + ((R * (P.card - E) : ℕ) : ℚ) / M
      ≤ ∑ n ∈ Finset.Icc m M, (1 : ℚ) / n := by sorry
