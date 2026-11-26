-- Prove2me | Theorems.Thm_Erdos287_cofactor_cut_congruence
-- name    : Erdos287.cofactor_cut_congruence
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:04:48.357665+00:00
-- url     : https://prove2.me/theorems/7656f0da-b21e-5d78-907e-36db404a3b50
-- title:
--   Cofactor congruence at an arbitrary prime-power cut
-- statement:
--   Let $D$ be a finite set of positive denominators with reciprocal sum one. Fix a prime $p$ and $e\ge1$. Suppose every cofactor $n/p^e$ of a selected multiple of $p^e$ divides $L$, and $p^j\mid L$. Then $p^{j+1}$ divides $\sum_{n\in D,\ p^e\mid n}L/(n/p^e)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.cofactor_cut_congruence (D : Finset ℕ) (p e L j : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hpos : ∀ n ∈ D, 0 < n) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hL : ∀ n ∈ D, p ^ e ∣ n → n / (p ^ e) ∣ L) (hLp : p ^ j ∣ L) :
    p ^ (j + 1) ∣ ∑ n ∈ D.filter (fun n => p ^ e ∣ n), L / (n / (p ^ e)) := by sorry
