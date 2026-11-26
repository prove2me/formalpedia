-- Prove2me | Theorems.Thm_Erdos287_reciprocal_clearing_and_modular_reduction
-- name    : Erdos287.reciprocal_clearing_and_modular_reduction
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:51:57.978959+00:00
-- url     : https://prove2.me/theorems/1110c7b0-5ba5-4eb5-b83f-4c3fcf8a1987
-- title:
--   Clearing unit-fraction denominators and reducing at a coprime modulus
-- statement:
--   Let $L>0$ be a common multiple of all denominators in a finite set $D$, and let $q$ be coprime to $L$. Write $W=\sum_{n\in D}L/n$. Then $\sum_{n\in D}1/n=1$ in $\mathbb Q$ exactly when $W=L$, and $\sum_{n\in D}n^{-1}=1$ in $\mathbb Z/q\mathbb Z$ exactly when $W\equiv L\pmod q$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reciprocal_clearing_and_modular_reduction (D : Finset ℕ) (q L : ℕ) (hL : 0 < L) (hcop : L.Coprime q)
    (hdiv : ∀ n ∈ D, n ∣ L) :
    ((∑ n ∈ D, (1 : ℚ) / n) = 1 ↔ (∑ n ∈ D, L / n) = L) ∧
    ((∑ n ∈ D, (n : ZMod q)⁻¹) = 1 ↔ (∑ n ∈ D, L / n) ≡ L [MOD q]) := by sorry
