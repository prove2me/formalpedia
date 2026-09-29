-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
-- name    : AlgebraicCurve.CurveModel.apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/1d3a8b1c-4d80-5b8f-9d85-d4ac01b4cfb1
-- title:
--   Birational ν hits the generic point and identifies function fields
-- statement:
--   Let $k$ be a field, let $C$ be a scheme with a morphism $c \colon C \to \operatorname{Spec} k$, and assume $C$ is integral. Let $F$ be a field with a $k$-algebra structure and let $M$ be a `CurveModel` for $F/k$: a scheme $M.C$ together with a morphism $M.\mathrm{toBase} \colon M.C \to \operatorname{Spec} k$ which is integral as a scheme, proper and smooth of relative dimension $1$, a ring isomorphism $M.\mathrm{ffEquiv} \colon F \cong \Gamma_{\mathrm{ff}}(M.C)$ onto the function field of $M.C$ carrying $\mathrm{algebraMap}\ k\ F$ to the canonical map `baseToFunctionField M.toBase` (the germ at the generic point of the global sections pulled back along $M.\mathrm{toBase}$), a bijection from the closed points of $M.C$ to the places of $F/k$ (valuation subrings of $F$ containing the image of $k$, proper and with principal ideals) such that for each closed point the image in $F$ of the stalk equals the corresponding valuation subring, and the property that every finite subset of $M.C$ lies in an affine open. Let $\nu \colon M.C \to C$ satisfy $\nu$ followed by $c$ equals $M.\mathrm{toBase}$, and suppose the stalk map of $\nu$ at the generic point of $M.C$ is an isomorphism. Then, with $C.\mathrm{functionField}$ regarded as a $k$-algebra via [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the image under $\nu$ of the generic point of $M.C$ is the generic point of $C$, and there exists a $k$-algebra isomorphism $F \simeq C.\mathrm{functionField}$.
--
--   This is the statement that a $k$-morphism from a smooth proper model of $F/k$ which is an isomorphism on stalks at the generic point is dominant and induces an identification of $F$ with the function field of the target; it is what transports data from the model to an arbitrary integral $k$-scheme $C$. It is used in the finiteness statements for integral closures and sections attached to such a $\nu$, and in the bound on the Euler characteristic of sections in terms of the genus of $F$ and the number of non-regular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ν.base (genericPoint M.C) = genericPoint C ∧ Nonempty (F ≃ₐ[k] C.functionField) := by sorry
