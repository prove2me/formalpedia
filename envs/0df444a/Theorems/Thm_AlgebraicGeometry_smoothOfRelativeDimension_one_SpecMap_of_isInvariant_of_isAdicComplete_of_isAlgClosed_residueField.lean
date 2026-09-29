-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/c86db7e9-54d0-5ebb-91bb-124b177a6e9a
-- title:
--   Invariants of a smooth relative curve over a complete DVR
-- statement:
--   Let $W$ be a commutative ring which is a domain and a discrete valuation ring, complete with respect to the adic filtration of its maximal ideal, and whose residue field is algebraically closed. Let $S$ and $A$ be commutative rings equipped with $W$-algebra structures and with an $S$-algebra structure on $A$ forming a scalar tower $W \to S \to A$, and assume the structure map $S \to A$ is injective (the $S$-action on $A$ is faithful). Let $G$ be a finite group acting on $A$ by ring automorphisms, the action commuting with the $W$-action and with the $S$-action on $A$, and assume `Algebra.IsInvariant S A G`, i.e. every element of $A$ fixed by all of $G$ lies in the image of $S$; together with faithfulness this identifies $S$ with $A^G$. Assume finally that the morphism $\operatorname{Spec} A \to \operatorname{Spec} W$ induced by $W \to A$ is smooth of relative dimension $1$. Then the morphism $\operatorname{Spec} S \to \operatorname{Spec} W$ induced by $W \to S$ is smooth of relative dimension $1$.
--
--   This is the affine, ring-theoretic form of the statement that the quotient of a smooth relative curve by a finite group action is again a smooth relative curve, over a complete discrete valuation ring with algebraically closed residue field and with no hypothesis on the orders of the stabilisers, so including the wildly ramified case (compare Katz–Mazur A7.1.1 and Deligne–Rapoport VI.6.7). It is the local core from which the corresponding statement over a Dedekind base, [`AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain), is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    [IsAlgClosed (ResidueField W)]
    {S A : Type} [CommRing S] [CommRing A]
    [Algebra W S] [Algebra W A] [Algebra S A] [IsScalarTower W S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G W A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W S))) := by sorry
