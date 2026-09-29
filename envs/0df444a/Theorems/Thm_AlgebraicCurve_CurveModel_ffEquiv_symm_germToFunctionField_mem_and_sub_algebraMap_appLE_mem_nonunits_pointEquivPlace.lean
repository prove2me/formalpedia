-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
-- name    : AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/09fe29f3-bc21-5df0-804d-0cb79dda07bb
-- title:
--   Value of a section at a K-point equals its residue
-- statement:
--   Let $K$ be an algebraically closed field and $L$ a field equipped with a $K$-algebra structure, and let $M$ be a `CurveModel K L`: a scheme $C = M.C$ over $K$ by a morphism $M.\mathrm{toBase} : C \to \operatorname{Spec} K$ which is integral, proper and smooth of relative dimension one, together with a ring isomorphism $M.\mathrm{ffEquiv} : L \cong C.\mathrm{functionField}$ carrying $\mathrm{algebraMap}\,K\,L$ to the germ at the generic point of the structure map, a bijection $M.\mathrm{placeOfPoint}$ from the closed points of $C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, distinct from $L$, whose ideals are principal) such that the image in $L$, under $M.\mathrm{ffEquiv}^{-1}$, of the stalk at a closed point is exactly the corresponding valuation subring, and the property that every finite set of points of $C$ lies in a single affine open. Let $U$ be a non-empty open subset of $C$, $s \in \Gamma(C, U)$, and let $z$ be a $K$-point of $C$, that is a morphism $\operatorname{Spec} K \to C$ whose composite with $M.\mathrm{toBase}$ is the identity, with the hypothesis $hz$ that all of $\operatorname{Spec} K$ lies in the preimage $z^{-1}(U)$. Write $\mathcal O_z \subseteq L$ for the valuation subring of the place $M.\mathrm{pointEquivPlace}\,z$ attached to $z$ (the closed point image of $z$, transported by $M.\mathrm{placeOfPoint}$). Then $M.\mathrm{ffEquiv}^{-1}$ of the germ of $s$ in the function field of $C$ lies in $\mathcal O_z$, and it differs from the image under $\mathrm{algebraMap}\,K\,L$ of the element of $K$ obtained by pulling $s$ back along $z$ (via $z.\mathrm{appLE}\,U\,\top\,hz$ and the isomorphism $\Gamma(\operatorname{Spec} K,\mathcal O) \cong K$) by an element of the non-units of $\mathcal O_z$, i.e. of its maximal ideal.
--
--   This is the value form of the dictionary between closed points of a smooth proper curve over an algebraically closed field and the places of its function field: a regular function on an open containing a rational point is integral at the associated place, and its residue there is its value at the point. It is used in the project wherever a section over an arbitrary open (for instance a chart pulled back along a morphism of models) has to be compared with its value at a $K$-point, for example in the existence of opens factoring a morphism through prescribed values, in vanishing statements for orders of residues, and in the convergence statements for pullbacks of sections over the complex numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(M.C, U))
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    M.ffEquiv.symm (M.C.germToFunctionField U s) ∈ (M.pointEquivPlace z).toValuationSubring ∧
    M.ffEquiv.symm (M.C.germToFunctionField U s) -
        algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (z.1.appLE U ⊤ hz s)) ∈
      (M.pointEquivPlace z).toValuationSubring.nonunits := by sorry
