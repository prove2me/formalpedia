-- Prove2me | Theorems.Thm_FiniteField_nonempty_algEquiv_of_card_eq
-- name    : FiniteField.nonempty_algEquiv_of_card_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/155e8954-abdb-5c94-ae47-48816e709543
-- title:
--   Finite extensions of equal cardinality are K-isomorphic
-- statement:
--   Let $K$ be a field (in the universe of types of type `Type`), and let $L_1$ and $L_2$ be two fields carrying $K$-algebra structures, each of which is finite as a type. Assume that $L_1$ and $L_2$ have the same number of elements, in the form $\mathrm{Nat.card}\,L_1 = \mathrm{Nat.card}\,L_2$. The conclusion is that the type of $K$-algebra isomorphisms $L_1 \simeq_{\text{alg}[K]} L_2$ is nonempty, i.e. there exists a ring isomorphism $L_1 \to L_2$ commuting with the structural maps from $K$. Note that the conclusion is the bare `Nonempty` assertion rather than a distinguished isomorphism: no canonical choice is made, and indeed in general none exists, the set of such isomorphisms being a coset of the Galois group. No finiteness hypothesis is placed on $K$ itself; it follows from the hypotheses, since $K$ embeds into the finite field $L_1$.
--
--   This is the relative uniqueness statement for finite fields: two finite fields of the same order containing a common base field $K$ are isomorphic over $K$, the version over an arbitrary base field of the classical uniqueness of the field with $q$ elements. It is used to identify finite residue fields of two local rings compatibly with a common subfield, and is cited by [`Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq`](thm.html#Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FiniteField_nonempty_algEquiv_of_card_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem FiniteField.nonempty_algEquiv_of_card_eq
    (K : Type) [Field K] (L₁ : Type) [Field L₁] [Algebra K L₁] [Finite L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [Finite L₂]
    (h : Nat.card L₁ = Nat.card L₂) :
    Nonempty (L₁ ≃ₐ[K] L₂) := by sorry
