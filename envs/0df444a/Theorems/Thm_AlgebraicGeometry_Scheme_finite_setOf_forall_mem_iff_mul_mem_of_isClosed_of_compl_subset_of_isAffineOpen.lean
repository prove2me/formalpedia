-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/0207853f-270d-548a-a8a8-4ec76da21e8c
-- title:
--   Finiteness of the stabiliser of a closed subset in a proper group scheme
-- statement:
--   Let $k$ be an algebraically closed field and let $t : X \to \operatorname{Spec} k$ be a proper morphism of schemes such that the object $\mathrm{Over.mk}\,t$ of the category of schemes over $\operatorname{Spec} k$ carries a group-object structure; the multiplication and the unit $1$ on the set of morphisms $\mathrm{Over.mk}(\mathbf 1_{\operatorname{Spec} k}) \to \mathrm{Over.mk}\,t$, that is on the set of sections of $t$ (the $k$-points of $X$), are those induced by this group-object structure. Let $Z \subseteq X$ be a closed subset of the underlying topological space, let $U$ be an open subscheme of $X$ which is affine, and assume that the complement $Z^{\mathrm c}$ is contained in $U$. Writing, for a $k$-point $z$, $z.\mathrm{left}$ for the induced morphism $\operatorname{Spec} k \to X$ and evaluating it at the closed point of $\operatorname{Spec} k$ to obtain a point of $X$, assume further that the point so attached to the unit $k$-point $1$ does not lie in $Z$. Then the set of $k$-points $x$ such that for every $k$-point $z$ the point attached to $z$ lies in $Z$ if and only if the point attached to $z \cdot x$ does, is finite.
--
--   This is the finiteness statement underlying Mumford's argument that an abelian variety is projective: the set-theoretic stabiliser, for right translation, of a closed set avoiding the origin whose complement sits inside an affine open is finite. It is used in the construction of an invertible sheaf with nonzero section and finite stabiliser on such a group scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [GrpObj (Over.mk t)]
    (Z : Set X) (hZ : IsClosed Z) (U : X.Opens) (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ (U : Set X))
    (he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t).left (IsLocalRing.closedPoint k) ∉ Z) :
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
      ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        z.left (IsLocalRing.closedPoint k) ∈ Z ↔ (z * x).left (IsLocalRing.closedPoint k) ∈ Z} := by sorry
