-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
-- name    : AlgebraicGeometry.isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/84e79542-823b-5714-8477-7fc26c6005b9
-- title:
--   Off one component, the other restricts isomorphically and smoothly
-- statement:
--   Let $k$ be a field and let $X$, $C_1$, $C_2$ be schemes. Given a morphism $x \colon X \to \operatorname{Spec} k$ with $X$ reduced, a morphism $c_1 \colon C_1 \to \operatorname{Spec} k$ which is smooth of relative dimension $1$, an element $i_1$ of $\mathtt{SchemeHomOver}\ c_1\ x$, that is, a morphism $i_1.1 \colon C_1 \to X$ together with the identity $i_1.1$ followed by $x$ equals $c_1$, and a further morphism $i_2 \colon C_2 \to X$, both $i_1.1$ and $i_2$ being closed immersions, assume that every point $z$ of $X$ lies in the set-theoretic image of $i_1.1$ or in that of $i_2$. Let $U$ be an open subscheme of $X$ whose underlying set is the complement of the image of the map on points of $i_2$. Then the restriction $i_1.1 \mid_ U \colon i_1.1^{-1}(U) \to U$ of $i_1.1$ over $U$ is an isomorphism, and the composite of the open immersion $U.\iota \colon U \to X$ with $x$ is smooth of relative dimension $1$.
--
--   This is the basic geometric fact that on a reduced curve covered by two closed subschemes, the open locus lying off the second one is cut out isomorphically by the first, hence inherits smoothness of relative dimension one from $C_1$. It is used in the relative Picard constructions for curves with two glued smooth components, where it supplies the local isomorphism and smoothness needed to make point twists at points away from the other component Cartier.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
    {k : Type u} [Field k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.base)
    (U : X.Opens) (hU : (U : Set X) = (Set.range i₂.base)ᶜ) :
    IsIso (i₁.1 ∣_ U) ∧ SmoothOfRelativeDimension 1 (U.ι ≫ x) := by sorry
