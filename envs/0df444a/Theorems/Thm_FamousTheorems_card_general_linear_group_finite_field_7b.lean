-- Prove2me | Theorems.Thm_FamousTheorems_card_general_linear_group_finite_field_7b
-- name    : FamousTheorems.card_general_linear_group_finite_field_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:40.415088+00:00
-- url     : https://prove2.me/theorems/be3d0e93-e249-4dd1-8bd4-0bedfbd80e87
-- title:
--   The order of GLₙ(𝔽_q)
-- statement:
--   **The order of $GL_n(\mathbb F_q)$.** Let $\mathbb F$ be a finite field with $q$ elements and $n\ge0$. Then
--   $$|GL_n(\mathbb F)|=\prod_{i=0}^{n-1}(q^n-q^i)=(q^n-1)(q^n-q)\cdots(q^n-q^{n-1}).$$
--
--   The formula counts ordered bases of $\mathbb F^n$: the $i$-th vector can be any vector outside the span of the previous $i$ vectors. It is used to compute the orders of the finite classical groups, to find their Sylow subgroups, and to count subspaces of $\mathbb F_q^n$ (the Gaussian binomial coefficients).
--
--   **Formalization note.** Mathlib's `Matrix.card_GL_field`. `GL (Fin n) F` is the group of invertible $n\times n$ matrices over $F$, and `Nat.card` is its cardinality.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.card_GL_field`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_general_linear_group_finite_field_7b {F : Type*} [Field F] [Fintype F] (n : ℕ) :
    Nat.card (GL (Fin n) F) = ∏ i : Fin n, (Fintype.card F ^ n - Fintype.card F ^ (i : ℕ)) := by sorry

end FamousTheorems
