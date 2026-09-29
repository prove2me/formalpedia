-- Prove2me | Theorems.Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero
-- name    : Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/34f5a132-4a37-5501-b8a5-92f239ac4239
-- title:
--   Pairs of L-points separate A ⊗_K A
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $A$ be a commutative $K$-algebra that is finite as a $K$-module, let $P$ be an arbitrary type (no finiteness assumed), and let $pt : P \to \operatorname{Hom}_{K\text{-alg}}(A, L)$ be a family of $K$-algebra homomorphisms $A \to L$. Assume that the $L$-algebra homomorphism $L \otimes_K A \to (P \to L)$ obtained by lifting the structure map $L \to (P \to L)$ (constant functions) together with the $K$-algebra homomorphism $A \to (P \to L)$, $a \mapsto (pt\,p\,(a))_{p \in P}$, is injective; concretely, injectivity of $c \otimes a \mapsto (c \cdot pt\,p\,(a))_{p}$. Let $x \in A \otimes_K A$ be such that for all $p, q \in P$ the image of $x$ under the $K$-algebra homomorphism $A \otimes_K A \to L$ lifting $pt\,p$ and $pt\,q$ — that is, $(pt\,p) \otimes (pt\,q)$ on pure tensors — vanishes. Then $x = 0$.
--
--   This is the statement that, for a finite commutative $K$-algebra $A$ whose $L$-points are separating (for instance when $A$ is split by $L$ with point set $P$), pairs of $L$-points separate elements of $A \otimes_K A$. It is the linear-algebra input used to verify identities in $A \otimes_K A$ pointwise, and is cited in the construction of bialgebra homomorphisms out of split finite Hopf algebras, in particular by [`HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero`](thm.html#HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    {P : Type*} (pt : P → (A →ₐ[K] L))
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (x : A ⊗[K] A)
    (hx : ∀ p q : P, Algebra.TensorProduct.lift (pt p) (pt q) (fun _ _ => Commute.all _ _) x = 0) :
    x = 0 := by sorry
