-- Prove2me | Theorems.Thm_Erdos287_high_cofactor_exclusions
-- name    : Erdos287.high_cofactor_exclusions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:21:41.681204+00:00
-- url     : https://prove2.me/theorems/8955c0c0-c0e4-437a-8c36-7b7da7147e23
-- title:
--   Uniform dense dyadic exclusion and high-layer prime restriction
-- statement:
--   Let $D$ be a finite set of positive denominators in $[m,M]$ summing reciprocally to one. If $M<3m$ and $M<5\cdot2^e$ with $e\ge1$, then $D$ contains no multiple of $2^e$. If $q=p^e$ for prime $p$, $2m\le M$, and $M-m<3q$, then a selected multiple of $q$ forces $p\in\{2,3,5,7,11,13,47\}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.high_cofactor_exclusions (D : Finset ℕ) (m M : ℕ) (hm : 0 < m)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) :
    (∀ e : ℕ, 1 ≤ e → M < 3 * m → M < 5 * 2 ^ e →
      D.filter (fun n => 2 ^ e ∣ n) = ∅) ∧
    (∀ p e : ℕ, p.Prime → 1 ≤ e → 2 * m ≤ M → M < m + 3 * p ^ e →
      p ∉ ({2, 3, 5, 7, 11, 13, 47} : Finset ℕ) →
        D.filter (fun n => p ^ e ∣ n) = ∅) := by sorry
