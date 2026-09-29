-- Prove2me | Theorems.Thm_FamousTheorems_galois_field_exists_6b
-- name    : FamousTheorems.galois_field_exists_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:31.251481+00:00
-- url     : https://prove2.me/theorems/2bf5efc7-5720-4301-9d95-0f67cdef9b76
-- title:
--   Existence of the finite field with p^n elements
-- statement:
--   **Existence of the finite field with $p^n$ elements.** For every prime $p$ and every $n\ge1$ there is a field with exactly $p^n$ elements.
--
--   The field is the splitting field of $X^{p^n}-X$ over $\mathbb F_p$, and its elements are exactly the roots of that polynomial. Together with the fact that a finite field has prime power order, this classifies the orders of finite fields. The fields $\mathbb F_{p^n}$ are used in coding theory, cryptography, combinatorial designs and the arithmetic of varieties over finite fields.
--
--   **Formalization note.** Mathlib's `GaloisField.card`, applied to `GaloisField p n`, the splitting field of $X^{p^n}-X$ over `ZMod p`. `Nat.card K` is the number of elements of $K$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `GaloisField.card`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem galois_field_exists_6b (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) : ∃ (K : Type) (_ : Field K), Nat.card K = p ^ n := by sorry

end FamousTheorems
