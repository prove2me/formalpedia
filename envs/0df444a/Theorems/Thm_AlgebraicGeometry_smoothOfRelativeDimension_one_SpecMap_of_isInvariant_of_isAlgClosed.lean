-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/082dfcda-5a21-5d85-a7d1-07e13e084f50
-- title:
--   Smoothness of the quotient of a smooth affine curve
-- statement:
--   Let $k$ be an algebraically closed field, and let $S$ and $A$ be commutative rings, each a $k$-algebra, with $A$ also an $S$-algebra in a way compatible with the $k$-algebra structures (a scalar tower $k \to S \to A$) and with the structure map $S \to A$ injective. Let $G$ be a finite group acting on $A$ by ring automorphisms, the action commuting with the $k$-action and with the $S$-action on $A$, and assume $A$ is invariant for $S$ under $G$ in the sense that every $a \in A$ fixed by all $g \in G$ lies in the image of $S \to A$. Assume finally that the morphism of affine schemes $\operatorname{Spec} A \to \operatorname{Spec} k$ induced by the structure map $k \to A$ is smooth of relative dimension $1$. Then the morphism $\operatorname{Spec} S \to \operatorname{Spec} k$ induced by $k \to S$ is smooth of relative dimension $1$. No hypothesis is imposed on $|G|$, on the stabilisers of the action, or on the domain or normality of $A$ or $S$.
--
--   This is the statement that the quotient of a smooth affine curve over an algebraically closed field by a finite group action is again a smooth affine curve, in the form: a $k$-subalgebra containing exactly the invariants inherits smoothness of relative dimension one. It is used to derive the corresponding smoothness statements in the Dedekind-domain case and in the adically complete case with algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed
    {k S A : Type u} [Field k] [IsAlgClosed k] [CommRing S] [CommRing A]
    [Algebra k S] [Algebra k A] [Algebra S A] [IsScalarTower k S A] [FaithfulSMul S A]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G k A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by sorry
