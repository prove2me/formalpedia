-- Prove2me | Theorems.Thm_Diaz_coeff_transfer_iff
-- name    : Diaz.coeff_transfer_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:44:39.57025+00:00
-- url     : https://prove2.me/theorems/86f5de0a-f5fc-49e7-87b0-9131968eb7b7
-- title:
--   Matrix coefficients transfer along a ring hom fixing the base, and vanish together
-- statement:
--   **Transfer of matrix coefficients along a ring homomorphism, and the equivalence it gives.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $\Phi : \mathbb{C} \to \mathbb{C}$ be a ring
--   homomorphism fixing $K$ pointwise. Let $M$ be a complex matrix, indexed by arbitrary finite
--   sets, and let $w$, $v$ be vectors with entries in $K$. Writing $\Phi(M)$ for $\Phi$ applied
--   entrywise,
--
--   $$\Phi\bigl(w^{\mathsf T} M v\bigr) \;=\; w^{\mathsf T}\,\Phi(M)\,v,$$
--
--   and consequently
--
--   $$w^{\mathsf T} M v = 0 \quad\Longleftrightarrow\quad w^{\mathsf T} \Phi(M) v = 0 .$$
--
--   **Proof.** Apply $\Phi$ to $\sum_{i,j} w_i M_{ij} v_j$: it preserves finite sums and products
--   and fixes each $w_i$ and $v_j$. The equivalence follows because $\Phi$ is injective — its
--   kernel is an ideal of the field $\mathbb{C}$ not containing $1$, hence zero.
--
--   **What is new here relative to the existing node.** `Diaz.coeff_transfer` already carries the
--   forward identity, over an arbitrary subfield $K$, for index types $\mathrm{Fin}\,m$ and
--   $\mathrm{Fin}\,n$. It does **not** carry the "consequently" clause. That clause is
--   the half that uses injectivity, and it is the half the intended application needs: one wants to
--   conclude that a coefficient *fails* to vanish downstream from its failing to vanish upstream,
--   which the identity alone does not give. This node states both halves, and takes the
--   index types to be arbitrary finite types rather than $\mathrm{Fin}\,m$, $\mathrm{Fin}\,n$:
--   $w^{\mathsf T} M v$ is a finite double sum, so finiteness of the index sets is what the
--   expression means rather than an extra hypothesis, and there is no reason to force a caller
--   through a numbering of the index set.
--
--   **Hypotheses.** None beyond those stated above. $M$ is an arbitrary complex matrix; only the
--   coefficient vectors are constrained to lie in $K$; $\Phi$ is only assumed to be a ring
--   homomorphism fixing $K$ — not surjective, not continuous, not conjugation-equivariant.
--
--   **Attribution.** The statement is Carlo Perassi's. His companion note to
--   https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9) does not state it separately: its case $K = \bar{\mathbb{Q}}$ is the coefficient equivalence behind the last clause of Theorem 5.1 there, and in this generality it is unpublished apart from this node. No novelty is claimed for the mathematics, which is elementary; the
--   contribution is the formalisation.
-- source:
--   Carlo Perassi, note accompanying https://github.com/carlok/diaz-modulus-lean (version 1.8, 24 September 2026, GitHub release note-v1.8), the coefficient equivalence behind the last clause of Theorem 5.1

import Mathlib

open ComplexConjugate

theorem Diaz.coeff_transfer_iff {K : Subfield ℂ} {m n : Type*} [Fintype m] [Fintype n]
    (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (M : Matrix m n ℂ) (w : m → ℂ) (v : n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j ∧
      ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by sorry
