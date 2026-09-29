-- Prove2me | Theorems.Thm_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul
-- name    : AlgebraicClosure.linearIndependent_of_linearIndependent_rat_of_forall_apply_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/22c3b8fc-f451-5159-ae2a-b0713dc8e36b
-- title:
--   Galois descent of linear independence over ℚ̄
-- statement:
--   Let $X$ be a type carrying an action of the group $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, let $\iota$ be an arbitrary index type, and let $F : \iota \to (X \to \overline{\mathbb Q})$ be a family of $\overline{\mathbb Q}$-valued functions on $X$. Assume that each $F_i$ is equivariant: $F_i(\sigma \cdot x) = \sigma(F_i(x))$ for all $i \in \iota$, all automorphisms $\sigma$ and all $x \in X$. Assume further that the family $F$ is linearly independent over $\mathbb Q$ as a family of elements of the $\mathbb Q$-vector space of functions $X \to \overline{\mathbb Q}$. The conclusion is that $F$ is linearly independent over $\overline{\mathbb Q}$ in the $\overline{\mathbb Q}$-vector space of functions $X \to \overline{\mathbb Q}$; here the two independence assertions refer to the same family of functions, viewed over the two scalar fields.
--
--   This is the Galois-descent form of Artin's independence lemma: the $\mathbb Q$-span of a family of Galois-equivariant functions is a $\mathbb Q$-form of its $\overline{\mathbb Q}$-span. It is used in the construction of finite flat models, via [`GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure`](thm.html#GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicClosure.linearIndependent_of_linearIndependent_rat_of_forall_apply_smul
    {X : Type} [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    {ι : Type} (F : ι → X → AlgebraicClosure ℚ)
    (hF : ∀ (i : ι) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F i (σ • x) = σ (F i x))
    (hind : LinearIndependent ℚ F) :
    LinearIndependent (AlgebraicClosure ℚ) F := by sorry
