-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_sub_algebraMap_mem_of_hasValue_placeOfPoint
-- name    : AlgebraicCurve.CurveModel.sub_algebraMap_mem_of_hasValue_placeOfPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/5241608f-ceb5-5682-9627-705fe6db9150
-- title:
--   Value at a place detects the prime of a closed point
-- statement:
--   Let $K$ be a field and $L$ a field extension of $K$, and let $M$ be a curve model of $L$ over $K$: an integral scheme $C = M.C$ together with a structure morphism $M.toBase : C \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$, a ring isomorphism $M.ffEquiv : L \cong K(C)$ compatible with the map $K \to K(C)$ induced by the structure morphism, and a bijection $M.placeOfPoint$ from the closed points of $C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, not all of $L$, and principal ideal rings) whose valuation subring at $x$ is the image in $L$ of the stalk $\mathcal{O}_{C,x}$. Let $B$ be a commutative $K$-algebra in the same universe as $K$, and let $G : \operatorname{Spec} B \to C$ be an open immersion with $G$ followed by $M.toBase$ equal to $\operatorname{Spec}$ of the structure map $K \to B$, the scheme-theoretic image $G(\operatorname{Spec} B)$ being nonempty. Let $z$ be a point of $\operatorname{Spec} B$ whose image $G(z)$ is a closed point of $C$, and let $f \in B$, $a \in K$. Transport $f$ to a section of $\mathcal{O}_C$ over the open image of $G$, take its germ in the function field $K(C)$, and pull back along $M.ffEquiv$ to an element $\tilde f \in L$. If the place $M.placeOfPoint(G(z))$ has value $a$ at $\tilde f$, that is, $\tilde f$ lies in the corresponding valuation subring and its residue in the residue field equals the image of $a$, then $f - a\cdot 1 \in B$ lies in the prime ideal of $B$ corresponding to $z$.
--
--   This is the converse half of the dictionary between evaluating a function on an affine chart of a curve model at a closed point and reading its value at the associated place: the value at the place determines the residue class of the chart function modulo the prime of the point. It is used in the construction of modular curve models, where place-level conditions on $q$-expansions must be converted into congruences inside an affine chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_sub_algebraMap_mem_of_hasValue_placeOfPoint.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.sub_algebraMap_mem_of_hasValue_placeOfPoint
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    {B : Type u} [CommRing B] [Algebra K B] (G : Spec (CommRingCat.of B) ⟶ M.C) [IsOpenImmersion G]
    (hG : G ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    [Nonempty (Scheme.Opens.toScheme (G ''ᵁ ⊤))]
    (z : ↥(Spec (CommRingCat.of B))) (hz : G.base z ∈ closedPoints M.C)
    (f : B) (a : K)
    (hv : (M.placeOfPoint ⟨G.base z, hz⟩).HasValue
      (M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤)
        ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv f)))) a) :
    f - algebraMap K B a ∈ z.asIdeal := by sorry
