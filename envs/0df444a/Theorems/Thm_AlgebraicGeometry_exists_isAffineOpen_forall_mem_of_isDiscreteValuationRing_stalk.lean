-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk
-- name    : AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/2e695b0f-3a2f-5e4a-b689-7c5b1a33fdb2
-- title:
--   Finitely many discrete valuation points lie in one affine open
-- statement:
--   Let $R$ be a commutative ring and let $X$ be a scheme (in a fixed universe) which is integral, i.e. irreducible and reduced. Let $f\colon X \to \operatorname{Spec} R$ be a morphism of schemes which is locally of finite type and separated. Let $S$ be a finite set of points of $X$ (a `Finset` of the underlying topological space of $X$) such that for every $x \in S$ the stalk $\mathcal{O}_{X,x}$ of the structure presheaf at $x$ is a discrete valuation ring. The assertion is that there exists an open subset $U$ of $X$ which is an affine open, i.e. the open subscheme it determines is affine, and which contains every point of $S$. No noetherian hypothesis is imposed on $R$ or on $X$, and no further restriction is placed on the points of $S$ beyond the condition on their local rings.
--
--   This is Lemma 4 of §6.4 of Bosch–Lütkebohmert–Raynaud's *Néron Models*, in the generality in which it is used there: on an integral scheme separated and locally of finite type over an affine base, finitely many points with discrete valuation local rings are simultaneously contained in an affine open. It is used in the project through the variant [`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing), which adds smoothness and specialisation conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [IsSeparated f]
    (S : Finset X) (hS : ∀ x ∈ S, IsDiscreteValuationRing (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by sorry
