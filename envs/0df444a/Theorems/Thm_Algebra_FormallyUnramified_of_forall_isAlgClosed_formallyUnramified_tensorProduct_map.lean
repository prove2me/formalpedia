-- Prove2me | Theorems.Thm_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
-- name    : Algebra.FormallyUnramified.of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/b1ec22f6-ff5f-58ed-a6f3-8fe813dedef3
-- title:
--   Formal unramifiedness from all geometric base changes
-- statement:
--   Let $S$, $A$ and $B$ be commutative rings in a single universe, with $A$ and $B$ algebras over $S$, $B$ an algebra over $A$, the three structures compatible in the sense that $S \to A \to B$ is a scalar tower, and $B$ of finite type as an $S$-algebra. Assume that for every field $k$ (in that same universe) which is algebraically closed and carries an $S$-algebra structure, the ring homomorphism underlying the base change $\mathrm{id}_k \otimes$ of the structure map $A \to B$, that is the $S$-algebra homomorphism $A \otimes_S k \to B \otimes_S k$ obtained by tensoring $\mathrm{IsScalarTower.toAlgHom}\,S\,A\,B$ with the identity of $k$, is formally unramified in the sense of `RingHom.FormallyUnramified`. Then the algebra $B$ over $A$ is formally unramified: for every $A$-algebra $R$ and every nilpotent (square-zero) thickening, lifts of $A$-algebra maps $B \to R$ are unique in the sense encoded by `Algebra.FormallyUnramified A B`. No separate hypothesis of finite type over $A$ is imposed; it follows from finite type over $S$.
--
--   This is the fibrewise criterion for unramifiedness: formal unramifiedness of a finite-type algebra may be tested on the geometric fibres over a base ring underneath. It is the ring-theoretic core used by [`AlgebraicGeometry.formallyUnramified_of_forall_geometricFibre_formallyUnramified`](thm.html#AlgebraicGeometry.formallyUnramified_of_forall_geometricFibre_formallyUnramified), the corresponding statement for morphisms of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.FormallyUnramified.of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
    {S : Type u} [CommRing S] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] [Algebra A B] [IsScalarTower S A B] [Algebra.FiniteType S B]
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra S k],
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)).toRingHom.FormallyUnramified) :
    Algebra.FormallyUnramified A B := by sorry
