-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
-- name    : AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/63de2845-e4f1-55f8-aad2-369aa05a04d5
-- title:
--   An H-fixed L-point descends to the fixed field
-- statement:
--   Let $F$ and $L$ be fields in the same universe with $L$ an $F$-algebra, and let $H$ be a subgroup of the group $L \simeq_{\mathrm{alg}[F]} L$ of $F$-algebra automorphisms of $L$. Let $X$ be a scheme and let $x \colon \operatorname{Spec}(L) \to X$ be a morphism of schemes, where $L$ is regarded as an object of `CommRingCat`. Assume that $x$ is invariant under $H$ in the sense that for every $\sigma \in H$, the morphism $\operatorname{Spec}$ of the ring homomorphism underlying $\sigma$, followed by $x$, equals $x$. Then there exists a morphism $y \colon \operatorname{Spec}(L^{H}) \to X$, where $L^{H} =$ `IntermediateField.fixedField H` is the intermediate field of elements of $L$ fixed by every element of $H$, such that $\operatorname{Spec}$ of the structure map $L^{H} \to L$, followed by $y$, equals $x$. No hypothesis of normality, separability or finiteness is imposed on $L/F$, and $H$ is an arbitrary subgroup; the conclusion asserts only the factorisation, with no uniqueness claim on $y$.
--
--   This is the elementary form of Galois descent for points: an $H$-invariant $L$-valued point of an arbitrary scheme factors through $\operatorname{Spec}$ of the fixed field, giving the inclusion $X(L)^{H} \subseteq \operatorname{im}\,X(L^{H})$ without invoking the Galois correspondence. It is used on the route through the Néron model and the relative Picard scheme, where an inertia-invariant point must be seen to be defined over the fixed field of the inertia subgroup; the Néron-extension and model-package lemmas cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq
    {F L : Type u} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {X : Scheme.{u}} (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : ∀ σ ∈ H, Spec.map (CommRingCat.ofHom (σ : L ≃ₐ[F] L).toRingEquiv.toRingHom) ≫ x = x) :
    ∃ y : Spec (CommRingCat.of ↥(IntermediateField.fixedField H)) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField H) L)) ≫ y = x := by sorry
