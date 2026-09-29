-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint
-- name    : AlgebraicGeometry.Scheme.forall_mem_iff_of_subset_union_preimage_or_disjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/c2f644d4-4686-5c61-b1e3-0e176d725aa1
-- title:
--   Translation invariance of D under z⁻¹z' for z,z'∈ Z
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a scheme over $k$ via a morphism $t : X \to \operatorname{Spec} k$ that is locally of finite type, with $X$ integral, and suppose the object $\operatorname{Over.mk} t$ of the category of schemes over $\operatorname{Spec} k$ carries a group-object structure whose underlying monoid object is commutative; $k$-points are the morphisms $\operatorname{Over.mk}(\mathrm{id}_{\operatorname{Spec} k}) \to \operatorname{Over.mk} t$ over $\operatorname{Spec} k$, which thus form a group, and each is evaluated at the closed point of $\operatorname{Spec} k$ to give a point of $X$. For a $k$-point $a$ write $T_a$ for the translation $\mathrm{id}_{\operatorname{Over.mk} t} \cdot (a \circ \text{terminal map})$, and let $T_a^{-1}D$ denote the preimage of a subset $D \subseteq X$ under the underlying continuous map of $T_a$ on $X$. Assume $D$ is closed and $D \neq X$, and $Z \subseteq X$ is closed and irreducible, and that for all $k$-points $a,b$ the set $Z$ is either contained in, or disjoint from, $T_a^{-1}D \cup T_b^{-1}D \cup T_{(ab)^{-1}}^{-1}D$. Then for all $k$-points $z,z'$ whose associated points of $X$ lie in $Z$, and every $k$-point $d$, the point of $d$ lies in $D$ if and only if the point of $d\cdot(z^{-1}z')$ lies in $D$.
--
--   This is the set-theoretic core of the argument of Mumford, *Abelian Varieties* §6 (Application 1), which deduces translation invariance of a closed subset from a contains-or-misses dichotomy for unions of three translates; it uses the existence of a $k$-point over each closed point of a scheme locally of finite type over an algebraically closed field ([`AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton`](thm.html#AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton)). It feeds the finiteness statements for the morphism to the projective presentation in [`AlgebraicGeometry.Scheme.Modules.ProjPresentation`](def/AlgebraicGeometry_ModulesProjPresentation.html#L20).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.forall_mem_iff_of_subset_union_preimage_or_disjoint
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] [IsIntegral X] [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (D : Set X) (hD : IsClosed D) (hD' : D ≠ Set.univ) (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z)
    (h : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Z ⊆ ((𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹' D) ∨
      Disjoint Z ((𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹' D))
    (z z' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t)
    (hz : z.left.base (IsLocalRing.closedPoint k) ∈ Z) (hz' : z'.left.base (IsLocalRing.closedPoint k) ∈ Z)
    (d : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    d.left.base (IsLocalRing.closedPoint k) ∈ D ↔ (d * (z⁻¹ * z')).left.base (IsLocalRing.closedPoint k) ∈ D := by sorry
