-- Prove2me | Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
-- name    : Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/7d8570d1-7b55-56e1-bb0e-94f4f447ef03
-- title:
--   Noether's finiteness theorem for finite group actions
-- statement:
--   Let $R$ be a commutative noetherian ring, and let $A$ and $B$ be commutative $R$-algebras with $B$ also an $A$-algebra, the maps forming a tower $R \to A \to B$ (so that the $R$-algebra structure on $B$ is induced by the one on $A$). Assume the $A$-action on $B$ is faithful in the strong sense recorded by `FaithfulSMul A B`, equivalently that $\mathrm{algebraMap}\ A\ B$ is injective. Let $G$ be a finite group acting on $B$ by ring automorphisms compatible with the additive and multiplicative structure, and assume `Algebra.IsInvariant A B G`, i.e. every $G$-invariant element of $B$ lies in the image of $A \to B$. Assume finally that $B$ is of finite type as an $R$-algebra. The conclusion is the conjunction of two assertions: $B$ is a finitely generated $A$-module, and $A$ is an $R$-algebra of finite type. The classical case is $A = B^G$ with the inclusion into $B$.
--
--   This is Noether's finiteness theorem for the invariants of a finite group acting on an algebra of finite type over a noetherian base, in the form where $A$ is any intermediate ring containing the invariants. It is used downstream for quotients of schemes of finite type by finite group actions, in particular in the study of invariant affine charts over a Dedekind base and of completions at closed points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type*) [CommRing A] [Algebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Algebra.FiniteType R B] :
    Module.Finite A B ∧ Algebra.FiniteType R A := by sorry
