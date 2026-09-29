-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_of_twoAffineLineCover
-- name    : AlgebraicCurve.CurveModel.exists_iso_of_twoAffineLineCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/0d6ce86e-e04d-54fe-81b6-d53143e2d908
-- title:
--   Two affine lines glued by inversion form a curve model of κ(X)
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $Z$ be a scheme and $z \colon Z \to \operatorname{Spec}\kappa$ a morphism, and let $i_0, i_1 \colon \operatorname{Spec}\kappa[X] \to Z$ be open immersions. Assume: each $i_j$ followed by $z$ is the morphism $\operatorname{Spec}\kappa[X] \to \operatorname{Spec}\kappa$ induced by the structure map $\kappa \to \kappa[X]$; the union of the set-theoretic images of $i_0$ and $i_1$ is all of $Z$; the open immersion $\operatorname{Spec}\kappa[X]_X \to \operatorname{Spec}\kappa[X]$ followed by $i_0$ coincides with the morphism $\operatorname{Spec}\kappa[X]_X \to \operatorname{Spec}\kappa[X]$ induced by the $\kappa$-algebra map $\kappa[X] \to \kappa[X]_X$ sending $X$ to the inverse of $X$, followed by $i_1$; and the intersection of the images of $i_0$ and $i_1$ is contained in the image of that localisation chart $\operatorname{Spec}\kappa[X]_X \to Z$. The conclusion asserts the existence of a curve model $M$ of $\operatorname{RatFunc}\kappa$ over $\kappa$ — an integral scheme $M.C$ with a proper, smooth of relative dimension one morphism $M.\mathrm{toBase}$ to $\operatorname{Spec}\kappa$, a ring isomorphism $\operatorname{RatFunc}\kappa \cong (M.C)$'s function field compatible with the maps from $\kappa$, a bijection from the closed points of $M.C$ onto the places of $\operatorname{RatFunc}\kappa$ over $\kappa$ (valuation subrings containing $\kappa$, proper, and principal ideal rings) matching each stalk with the corresponding valuation subring, and with every finite set of points contained in an affine open — together with an isomorphism $e \colon M.C \cong Z$ such that $e$ followed by $z$ is $M.\mathrm{toBase}$.
--
--   This is the recognition statement for $\mathbb P^1_\kappa$ presented by its two standard affine charts: any $\kappa$-scheme covered by two copies of the affine line glued along the punctured line by inversion is, over $\kappa$, the underlying scheme of a smooth proper model of the rational function field $\kappa(X)$. It is obtained from the existence of such a model on the explicitly glued two-chart scheme, and serves the treatment of the rational (exceptional) case in the curve-theoretic input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_iso_of_twoAffineLineCover.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Polynomial

theorem AlgebraicCurve.CurveModel.exists_iso_of_twoAffineLineCover
    (κ : Type u) [Field κ] [IsAlgClosed κ] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of κ))
    (i₀ i₁ : Spec (CommRingCat.of (Polynomial κ)) ⟶ Z) [IsOpenImmersion i₀] [IsOpenImmersion i₁]
    (hi₀ : i₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap κ (Polynomial κ))))
    (hi₁ : i₁ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap κ (Polynomial κ))))
    (hcov : Set.range i₀.base ∪ Set.range i₁.base = Set.univ)
    (hglue : Spec.map (CommRingCat.ofHom (algebraMap (Polynomial κ) (Localization.Away (X : Polynomial κ)))) ≫ i₀ =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := κ)
        (IsLocalization.Away.invSelf (S := Localization.Away (X : Polynomial κ)) (X : Polynomial κ))).toRingHom) ≫ i₁)
    (hmeet : Set.range i₀.base ∩ Set.range i₁.base ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial κ) (Localization.Away (X : Polynomial κ)))) ≫ i₀).base) :
    ∃ (M : CurveModel κ (RatFunc κ)) (e : M.C ≅ Z), e.hom ≫ z = M.toBase := by sorry
