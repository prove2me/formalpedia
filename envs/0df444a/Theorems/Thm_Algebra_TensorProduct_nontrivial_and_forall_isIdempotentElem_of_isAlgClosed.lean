-- Prove2me | Theorems.Thm_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
-- name    : Algebra.TensorProduct.nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/15786cc2-531d-5aee-9812-cd6e03015986
-- title:
--   Trivial idempotents persist under base change from an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field and let $R$ be a commutative $k$-algebra, all in a fixed universe, which is finite as a $k$-module and non-trivial (so $0 \neq 1$ in $R$), and assume that every idempotent $e \in R$, i.e. every $e$ with $e \cdot e = e$, equals $0$ or $1$. Let $K$ be any field equipped with a $k$-algebra structure (no separability, algebraicity or finiteness is assumed of $K/k$). The conclusion is the conjunction of two assertions about the base change $K \otimes_k R$, taken as a commutative ring: first, $K \otimes_k R$ is non-trivial, that is $0 \neq 1$ in it; and second, every idempotent element $e$ of $K \otimes_k R$ satisfies $e = 0$ or $e = 1$. Thus the property 'non-zero with only the trivial idempotents' is inherited by $K \otimes_k R$ from $R$.
--
--   This is the commutative-algebra core of the statement that a connected scheme which is finite over an algebraically closed field stays connected after any field base change. It is used in the proof of [`AlgebraicGeometry.geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace`](thm.html#AlgebraicGeometry.geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace), which deduces geometric connectedness of a proper connected scheme over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem Algebra.TensorProduct.nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (R : Type u) [CommRing R] [Algebra k R]
    [Module.Finite k R] [Nontrivial R] (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial (K ⊗[k] R) ∧ ∀ e : K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 := by sorry
