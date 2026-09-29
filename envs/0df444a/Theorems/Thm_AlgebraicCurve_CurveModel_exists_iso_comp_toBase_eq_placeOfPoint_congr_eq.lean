-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
-- name    : AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/2fda3ef0-d523-57bc-96d1-c5c73b27c56b
-- title:
--   Uniqueness of smooth proper models, compatibly with places
-- statement:
--   Let $K$ be a field and let $F$, $F'$ be fields equipped with $K$-algebra structures, and let $\varphi : F \simeq_K F'$ be an isomorphism of $K$-algebras. Let $M$ be a `CurveModel` for $K$ and $F$ and $M'$ one for $K$ and $F'$; that is, each consists of an integral scheme $M.C$ together with a morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$, a ring isomorphism $M.\mathrm{ffEquiv}$ from the given field onto the function field of $M.C$ commuting with the two structure maps from $K$, and a bijection $M.\mathrm{placeOfPoint}$ from the closed points of $M.C$ onto the places of the field over $K$ (a place being a valuation subring containing the image of $K$, distinct from the whole field, and a principal ideal ring) such that for each closed point $x$ the image in the field, via $M.\mathrm{ffEquiv}^{-1}$, of the stalk at $x$ inside the function field is exactly the valuation subring of $M.\mathrm{placeOfPoint}(x)$, together with the property that every finite set of points of $M.C$ lies in a single affine open. The assertion is that there exist an isomorphism of schemes $e : M.C \cong M'.C$ with $e$ followed by $M'.\mathrm{toBase}$ equal to $M.\mathrm{toBase}$, and, for every closed point $x$ of $M.C$, the point $e(x)$ (closed, since $e$ is a homeomorphism) satisfies $M'.\mathrm{placeOfPoint}(e(x)) = \mathrm{Place.congrRingEquiv}\,\varphi\,(M.\mathrm{placeOfPoint}(x))$, the place of $F'$ whose valuation subring is the preimage under $\varphi^{-1}$ of the valuation subring of $M.\mathrm{placeOfPoint}(x)$.
--
--   This is the uniqueness half of the correspondence between function fields of one variable over $K$ and smooth proper curves over $K$, in the form that a $K$-isomorphism of function fields is induced by a unique isomorphism of models, compatible with the bijections between closed points and places. It is used to transport place-theoretic data between models, for instance in the semilinear comparison with Frobenius twists and in the analysis of degenerations of Deligne–Rapoport models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Pic0Congr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
    {K : Type u} [Field K]
    {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (φ : F ≃ₐ[K] F') (M : CurveModel K F) (M' : CurveModel K F') :
    ∃ (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase),
      ∀ x : closedPoints M.C,
        M'.placeOfPoint ⟨e.hom.base x.1, by
            show IsClosed ({e.hom.base x.1} : Set M'.C)
            rw [← Set.image_singleton]
            exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isClosedMap _ x.2⟩
          = Place.congrRingEquiv φ.toRingEquiv (fun a => φ.commutes a) (M.placeOfPoint x) := by sorry
