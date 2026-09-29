-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range
-- name    : AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d2aa1602-4e64-5235-8b1c-495f9bdd2405
-- title:
--   A reduced scheme covered by two affine closed subschemes is affine
-- statement:
--   Let $X$, $Z_1$, $Z_2$ be schemes and let $i_1 : Z_1 \to X$, $i_2 : Z_2 \to X$ be morphisms of schemes. Assume that $i_1$ and $i_2$ are closed immersions (`IsClosedImmersion`), that $Z_1$ and $Z_2$ are affine schemes (`IsAffine`), that $X$ is reduced (`IsReduced`, i.e. all its local rings, equivalently all rings of sections on opens, are reduced), and that the two closed subsets covered by the images of the underlying continuous maps exhaust $X$, that is $\operatorname{range}(i_1)_{\mathrm{base}} \cup \operatorname{range}(i_2)_{\mathrm{base}} = X$ as sets of points. The conclusion is that $X$ is itself an affine scheme, i.e. the canonical morphism $X \to \operatorname{Spec} \Gamma(X, \mathcal{O}_X)$ is an isomorphism. No separatedness, quasi-compactness or finiteness hypothesis on $X$ is imposed; affineness of $X$ is asserted as a proposition, not accompanied by an explicit description of $\Gamma(X,\mathcal{O}_X)$ as a fibre product.
--
--   This is the two-subscheme case of the statement that a reduced scheme which is set-theoretically the union of finitely many affine closed subschemes is affine; the mechanism is that on an affine open $\operatorname{Spec} A \subseteq X$ the two closed subschemes are cut out by ideals $I_1$, $I_2$ with $I_1 \cap I_2$ contained in the nilradical, hence zero, so that $A$ embeds into $A/I_1 \times A/I_2$ as the fibre product over $A/(I_1+I_2)$, which is the content of the cited ideal-theoretic lemma. It is used to derive the version for an arbitrary finite family of affine closed subschemes whose images cover, [`AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ`](thm.html#AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range
    (X Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (h₁ : IsClosedImmersion i₁) (h₂ : IsClosedImmersion i₂)
    (hZ₁ : IsAffine Z₁) (hZ₂ : IsAffine Z₂)
    (hred : IsReduced X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    IsAffine X := by sorry
