-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
-- name    : AlgebraicCurve.CurveModel.exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/e779afb7-3f96-54ec-8d2f-1bdbed42e39f
-- title:
--   Finite surjection of curve models induces a function-field embedding
-- statement:
--   Let $k$ be an algebraically closed field and let $L$, $L'$ be fields equipped with $k$-algebra structures. Let $M$ be a curve model of $L$ over $k$ and $M'$ one of $L'$ over $k$: thus $M.C$ is an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$ via $M.\mathrm{toBase}$, together with a ring isomorphism $M.\mathrm{ffEquiv} : L \cong \mathcal{K}(M.C)$ compatible with the structure map from $k$, a bijection between the closed points of $M.C$ and the places of $L$ over $k$ (valuation subrings of $L$ containing $k$, proper, and principal ideal rings) matching stalks with valuation rings, and the property that every finite set of points lies in an affine open; similarly for $M'$. Let $d : M'.C \to M.C$ be a morphism with $d$ followed by $M.\mathrm{toBase}$ equal to $M'.\mathrm{toBase}$, which is finite and surjective on points. The assertion is that there exist a $k$-algebra homomorphism $\varphi : L \to L'$ making $L'$ a finite $L$-module along $\varphi$ and integral as a ring map, such that, first, for every open $U \subseteq M.C$ with $U$ and $d^{-1}U$ nonempty and every $t \in \Gamma(M.C, U)$, $\varphi$ carries the element of $L$ corresponding under $M.\mathrm{ffEquiv}$ to the germ of $t$ at the generic point to the element of $L'$ corresponding under $M'.\mathrm{ffEquiv}$ to the germ of $d^{\ast}t$ on $d^{-1}U$; and second, for every place $R$ of $L'$ over $k$, the $k$-point of $M.C$ (a section of $M.\mathrm{toBase}$) attached by $M.\mathrm{pointEquivPlace}$ to the place obtained by pulling back the valuation subring of $R$ along $\varphi$ is the $k$-point of $M'.C$ attached to $R$ followed by $d$.
--
--   This is the standard passage from a finite surjective morphism of smooth proper curves over an algebraically closed field to the induced finite integral extension of function fields, together with the compatibility between the geometric points of the curves and the restriction of places. It serves as the converse to the construction producing a morphism of models from a given embedding of function fields, and is used in the construction of the moduli tower in the Čerednik–Drinfel'd setting, where it supplies the tower embeddings attached to the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.lean

import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
    (k : Type) [Field k] [IsAlgClosed k]
    {L L' : Type} [Field L] [Field L'] [Algebra k L] [Algebra k L']
    (M : CurveModel k L) (M' : CurveModel k L')
    (d : M'.C ⟶ M.C) (hd : d ≫ M.toBase = M'.toBase) [IsFinite d] (hsurj : Function.Surjective d.base) :
    ∃ (φ : L →ₐ[k] L') (hfin : FiniteAlong k φ) (hint : φ.toRingHom.IsIntegral),
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (d ⁻¹ᵁ U))]
        (t : Γ(M.C, U)),
        φ (M.ffEquiv.symm (M.C.germToFunctionField U t)) =
          M'.ffEquiv.symm (M'.C.germToFunctionField (d ⁻¹ᵁ U) ((d.app U).hom t))) ∧
      ∀ R : Place k L',
        (M.pointEquivPlace.symm (R.restrictAlong φ hint)).1 = (M'.pointEquivPlace.symm R).1 ≫ d := by sorry
