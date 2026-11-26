-- Prove2me | Theorems.Thm_Erdos287_sparse_prime_power_layer
-- name    : Erdos287.sparse_prime_power_layer
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:48:09.990905+00:00
-- url     : https://prove2.me/theorems/90dea04c-815a-5f16-93d3-c0ed50a0299a
-- title:
--   Exact cancellation in a prime-power layer with small cofactors
-- statement:
--   Let $D\subseteq[m,M]$ have positive denominators with reciprocal sum $1$. Let $q=p^e$ with $p$ prime and $e\ge1$, and suppose $M<m+2q$ and $M<4q$. Then the set $H$ of selected multiples of $q$ is empty, or $p=3$ and $H=\{q,2q\}$, or $p=5$ and $H=\{2q,3q\}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.sparse_prime_power_layer (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hspan : M < m + 2 * p ^ e) (hmax : M < 4 * p ^ e) :
    let q := p ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨ (p = 3 ∧ H = ({q, 2 * q} : Finset ℕ)) ∨
      (p = 5 ∧ H = ({2 * q, 3 * q} : Finset ℕ)) := by sorry
