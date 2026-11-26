-- Prove2me | Theorems.Thm_Erdos287_unit_sum_reconstruction_from_coprime_modulus
-- name    : Erdos287.unit_sum_reconstruction_from_coprime_modulus
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:54:07.508788+00:00
-- url     : https://prove2.me/theorems/d6644165-24f1-44e2-9e11-d1f4c176733c
-- title:
--   Exact reconstruction of a unit-fraction sum from a single coprime modulus
-- statement:
--   Let $L>0$ be a common multiple of the denominators in $D$, let $W=\sum_{n\in D}L/n$, and let $q$ be coprime to $L$. If $|W-L|<q$, the exact rational reciprocal sum equals one if and only if its modular inverse sum in $\mathbb Z/q\mathbb Z$ is one.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.unit_sum_reconstruction_from_coprime_modulus (D : Finset ℕ) (L q : ℕ) (hL : 0 < L) (hcop : L.Coprime q)
    (hD : ∀ n ∈ D, n ∣ L)
    (hbound : Int.natAbs (((∑ n ∈ D, L / n : ℕ) : ℤ) - L) < q) :
    (∑ n ∈ D, (1 : ℚ) / n) = 1 ↔ (∑ n ∈ D, (n : ZMod q)⁻¹) = 1 := by sorry
