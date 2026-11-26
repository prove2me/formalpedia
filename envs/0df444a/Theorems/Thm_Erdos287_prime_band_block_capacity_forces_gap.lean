-- Prove2me | Theorems.Thm_Erdos287_prime_band_block_capacity_forces_gap
-- name    : Erdos287.prime_band_block_capacity_forces_gap
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:31:38.068798+00:00
-- url     : https://prove2.me/theorems/d5b6f042-8f54-516a-92c2-ef3cae357bdd
-- title:
--   Joint omission capacity across large-prime layers
-- statement:
--   Let $D\subseteq[m,M]$ have reciprocal sum one, and let $H$ be a set of certified omissions inside the interval. For a finite set $P$ of eligible primes at least $Y>\sqrt M$, let $U$ contain all positions in their multiple layers that have no neighbor in $H$. Partition $U$ into singleton and consecutive-pair blocks. Suppose each layer has at least $R$ positions and $\lfloor M/p\rfloor\le B$ for each $p\in P$, with $B\operatorname{lcm}(1,\ldots,B)<Y^{K+1}$. If the number of blocks is less than $R\max(0,|P|-E)$, where $E=(B+1)^2K\sum_{j<R}\binom Bj$, then two consecutive integers in $[m,M]$ are omitted.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.prime_band_block_capacity_forces_gap (D H P U J : Finset ℕ) (block : ℕ → ℕ)
    (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D)
    (hYM : M < Y ^ 2) (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1))
    (hcover : ∀ n ∈ Finset.Icc m M, n - 1 ∉ H → n + 1 ∉ H →
      (∃ p ∈ P, p ∣ n) → n ∈ U)
    (hblock : ∀ n ∈ U, block n ∈ J)
    (hpair : ∀ x ∈ U, ∀ y ∈ U, block x = block y →
      x = y ∨ x + 1 = y ∨ y + 1 = x)
    (hsmall :
      J.card < R * (P.card - ((B + 1) * (B + 1)) *
        (∑ j ∈ Finset.range R, B.choose j) * K)) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by sorry
