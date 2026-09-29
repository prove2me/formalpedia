-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
-- name    : AlgebraicCurve.CurveModel.exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/5036d37b-9bcf-508e-8c4e-d997c51db840
-- title:
--   Function-field automorphism induces an automorphism of the curve model
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $L$ a field that is a $K$-algebra, both in the same universe. Let $M$ be a `CurveModel K L`: a scheme $M.C$ together with a morphism $M.toBase : M.C \to \operatorname{Spec} K$ such that $M.C$ is integral, $M.toBase$ is proper and smooth of relative dimension $1$, a ring isomorphism $M.ffEquiv : L \cong \Gamma$ of $L$ with the function field of $M.C$ carrying $\operatorname{algebraMap}_{K,L}$ to the structure map $K \to \Gamma$ induced by $M.toBase$, a bijection $M.placeOfPoint$ from the closed points of $M.C$ to the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, not equal to $L$, and principal ideal rings) such that the image of the stalk at each closed point inside $\Gamma$ corresponds under $M.ffEquiv^{-1}$ to the valuation subring of the associated place, and the property that every finite set of points of $M.C$ lies in an affine open. Let $V : L \simeq_K L$ be a $K$-algebra automorphism and $hV$ the hypothesis that its underlying ring homomorphism is integral. The conclusion asserts the existence of an isomorphism $h : M.C \cong M.C$ such that: $h.hom$ followed by $M.toBase$ equals $M.toBase$, so $h$ is an isomorphism over $\operatorname{Spec} K$; on the generic point $\eta$ of $M.C$, the canonical morphism $\operatorname{Spec}$ of the stalk at $\eta$ into $M.C$ followed by $h.hom$ equals $\operatorname{Spec}$ of the ring homomorphism $M.ffEquiv \circ V \circ M.ffEquiv^{-1}$ of $\Gamma$ followed by that same morphism; and for every place $P$ of $L/K$, the section $\operatorname{Spec} K \to M.C$ of $M.toBase$ corresponding to $P$ under the bijection $M.pointEquivPlace$, followed by $h.hom$, is the section corresponding to $P.restrictAlong\,V\,hV$, the place whose valuation subring is the preimage of that of $P$ under $V$.
--
--   This is the statement that a $K$-automorphism of the function field of a smooth proper curve model is realised by an automorphism of the model over $\operatorname{Spec} K$, together with the explicit description of its effect on the generic point and on the $K$-points, which are indexed by the places of $L/K$. It is used in the Čerednik–Drinfeld part of the development, in the identification of the action of Atkin–Lehner type involutions on germs at points of a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv.lean

import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {L : Type u} [Field L] [Algebra K L]
    (M : CurveModel K L) (V : L ≃ₐ[K] L) (hV : (V : L →ₐ[K] L).toRingHom.IsIntegral) :
    ∃ h : M.C ≅ M.C, h.hom ≫ M.toBase = M.toBase ∧
      M.C.fromSpecStalk (genericPoint M.C) ≫ h.hom =
        Spec.map (CommRingCat.ofHom
          (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      ∀ P : Place K L,
        (M.pointEquivPlace.symm P).1 ≫ h.hom = (M.pointEquivPlace.symm (P.restrictAlong (V : L →ₐ[K] L) hV)).1 := by sorry
