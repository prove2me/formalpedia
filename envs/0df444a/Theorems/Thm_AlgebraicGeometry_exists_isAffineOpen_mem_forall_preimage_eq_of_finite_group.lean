-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group
-- name    : AlgebraicGeometry.exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/4a4535a5-8b72-585d-a1a9-b1c219e78068
-- title:
--   G-stable affine neighbourhood in a separated scheme
-- statement:
--   Let $A$ be a commutative ring, let $X$ be a scheme and let $f : X \to \operatorname{Spec} A$ be a separated morphism. Assume that every finite subset $S$ of the underlying space of $X$ is contained in some affine open $U$ of $X$. Let $G$ be a finite group, let $a : G \to \operatorname{Aut} X$ be a group homomorphism into the group of scheme automorphisms of $X$, and assume that each automorphism lies over the base, i.e. the underlying morphism of $a(g)$ followed by $f$ equals $f$ for every $g \in G$. Then for every point $x$ of $X$ there is an open subscheme $U \subseteq X$ which is affine, contains $x$, and is stable in the strong sense that the scheme-theoretic preimage of $U$ under the morphism underlying $a(g)$ equals $U$ for every $g \in G$.
--
--   This is the standard existence statement for $G$-stable affine charts around a point of a separated scheme carrying an action of a finite group, the geometric input for forming quotients by finite groups chart by chart. It is used in the construction of the quotient of a flat proper $\pi$-adic tower by a finite group, via [`AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat`](thm.html#AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group
    (A : Type) [CommRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    (haff : ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X))
    (G : Type) [Group G] [Finite G] (a : G →* Aut X) (ha : ∀ g : G, (a g).hom ≫ f = f) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (a g).hom ⁻¹ᵁ U = U := by sorry
