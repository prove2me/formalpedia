-- Prove2me | Theorems.Thm_Erdos287_dense_prime_power_endpoint_restrictions
-- name    : Erdos287.dense_prime_power_endpoint_restrictions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:50:25.207822+00:00
-- url     : https://prove2.me/theorems/dd246e46-dcb5-4a88-9ec2-a6782d269de0
-- title:
--   Prime-power endpoint restrictions in a dense interval
-- statement:
--   An exact unit reciprocal sum with first denominator $m$ and last denominator $M<3m$ has the following restrictions. If $m=p^e$ for a prime $p$ and $e\ge1$, then $p=3$ and $2m$ is selected. If $p^e\mid M$ and $M\le3p^e$, then $M=2\cdot3^e$ with $3^e$ selected, or $M=3\cdot5^e$ with $2\cdot5^e$ selected.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.dense_prime_power_endpoint_restrictions (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hmD : m ∈ D) (hMD : M ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (hratio : M < 3 * m) :
    (m = p ^ e → p = 3 ∧ 2 * m ∈ D) ∧
    (p ^ e ∣ M → M ≤ 3 * p ^ e →
      (p = 3 ∧ M = 2 * p ^ e ∧ p ^ e ∈ D) ∨
      (p = 5 ∧ M = 3 * p ^ e ∧ 2 * p ^ e ∈ D)) := by sorry
