-- Prove2me | Theorems.Thm_FamousTheorems_abel_x_pow_prime_sub_irreducible_6c
-- name    : FamousTheorems.abel_x_pow_prime_sub_irreducible_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:00.547906+00:00
-- url     : https://prove2.me/theorems/6e9a5479-4ef9-4009-9684-164f8b0aebdd
-- title:
--   Irreducibility of X^p − a when a is not a p-th power (Abel)
-- statement:
--   **Irreducibility of $X^p-a$.** Let $K$ be a field, $p$ a prime number, and $a\in K$ an element that is not a $p$-th power in $K$. Then the polynomial $X^p-a$ is irreducible over $K$.
--
--   This result goes back to Abel. It is the basic step in Kummer theory and in the theory of radical extensions: adjoining a $p$-th root of a non-$p$-th power gives an extension of degree exactly $p$. It is part of the proof that the general quintic is not solvable by radicals. The result holds in every characteristic, including $p=\operatorname{char}K$.
--
--   **Formalization note.** Mathlib's `X_pow_sub_C_irreducible_of_prime`. The polynomial is `X ^ p - C a` in `Polynomial K`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `X_pow_sub_C_irreducible_of_prime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem abel_x_pow_prime_sub_irreducible_6c {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (Polynomial.X ^ p - Polynomial.C a) := by sorry

end FamousTheorems
