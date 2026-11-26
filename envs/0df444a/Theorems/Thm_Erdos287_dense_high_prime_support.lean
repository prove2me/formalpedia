-- Prove2me | Theorems.Thm_Erdos287_dense_high_prime_support
-- name    : Erdos287.dense_high_prime_support
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:25:34.728125+00:00
-- url     : https://prove2.me/theorems/161e6a06-0f11-5660-b2f4-7d09875ac8e0
-- title:
--   Five possible patterns in a high prime-power layer of a dense representation
-- statement:
--   Suppose $D\subseteq[m,M]$ consists of positive denominators with reciprocal sum one and $5m\le2M<6m$. Let $q=p^e$ for prime $p$ and $e\ge1$, with $M-m<3q$. Any nonempty selected $q$-layer has cofactor set $\{1,2\}$ or $\{2,4\}$ for $p=3$, $\{2,3\}$ for $p=5$, $\{3,4\}$ for $p=7$, or $\{2,3,4\}$ for $p=13$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.dense_high_prime_support (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hratio : M < 3 * m) (hspread : 5 * m ≤ 2 * M) (hspan : M < m + 3 * p ^ e) :
    let q := p ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨
      (p = 3 ∧ H = {q, 2 * q}) ∨
      (p = 5 ∧ H = {2 * q, 3 * q}) ∨
      (p = 7 ∧ H = {3 * q, 4 * q}) ∨
      (p = 3 ∧ H = {2 * q, 4 * q}) ∨
      (p = 13 ∧ H = {2 * q, 3 * q, 4 * q}) := by sorry
