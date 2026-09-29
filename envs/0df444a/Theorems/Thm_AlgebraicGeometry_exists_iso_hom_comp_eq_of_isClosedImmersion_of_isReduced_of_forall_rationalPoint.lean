-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint
-- name    : AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/84dfe99a-2eec-5a84-a9da-30cee47413b9
-- title:
--   Reduced closed subschemes determined by their k-points
-- statement:
--   Let $k$ be an algebraically closed field, let $Y$ be a scheme and let $f : Y \to \operatorname{Spec} k$ be a morphism that is locally of finite type. Let $i_1 : Z_1 \to Y$ and $i_2 : Z_2 \to Y$ be closed immersions with $Z_1$ and $Z_2$ reduced schemes. Assume that for every morphism $y : \operatorname{Spec} k \to Y$ which is a section of $f$, in the sense that $y$ followed by $f$ is the identity of $\operatorname{Spec} k$, the morphism $y$ factors through $i_1$ if and only if it factors through $i_2$; that is, there exists $z : \operatorname{Spec} k \to Z_1$ with $z$ followed by $i_1$ equal to $y$ exactly when there exists $z : \operatorname{Spec} k \to Z_2$ with $z$ followed by $i_2$ equal to $y$. The conclusion is that there is an isomorphism of schemes $e : Z_1 \cong Z_2$ whose underlying morphism, followed by $i_2$, equals $i_1$; so the two closed subschemes of $Y$ coincide, compatibly with their inclusions into $Y$.
--
--   This is the statement that a reduced closed subscheme of a scheme locally of finite type over an algebraically closed field is determined, as a subscheme of $Y$, by the set of $k$-rational points of $Y$ lying on it. It is used to compare two finite flat closed subgroup schemes of a Néron model that have the same rational points on their generic fibres, in [`ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff`](thm.html#ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint
    {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {Z₁ Z₂ : Scheme.{0}} (i₁ : Z₁ ⟶ Y) (i₂ : Z₂ ⟶ Y) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced Z₁] [IsReduced Z₂]
    (h : ∀ y : Spec (CommRingCat.of k) ⟶ Y, y ≫ f = 𝟙 _ →
      ((∃ z : Spec (CommRingCat.of k) ⟶ Z₁, z ≫ i₁ = y) ↔ (∃ z : Spec (CommRingCat.of k) ⟶ Z₂, z ≫ i₂ = y))) :
    ∃ e : Z₁ ≅ Z₂, e.hom ≫ i₂ = i₁ := by sorry
