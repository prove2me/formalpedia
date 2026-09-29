-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap
-- name    : AlgebraicCurve.CurveModel.finite_integralClosure_sections_of_isIso_stalkMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/a0960d75-f1b2-5291-9020-cb61867fd8f5
-- title:
--   Finiteness of the integral closure of sections on an affine chart
-- statement:
--   Let $k$ be an algebraically closed field, let $C$ be a scheme equipped with a morphism $c : C \to \operatorname{Spec} k$, assume $C$ integral and $c$ proper, and let $F$ be a field with a $k$-algebra structure. Let $M$ be a `CurveModel` for $F$ over $k$: a scheme $M.C$ with a morphism $M.toBase : M.C \to \operatorname{Spec} k$ such that $M.C$ is integral, $M.toBase$ is proper and smooth of relative dimension $1$, together with a ring isomorphism $F \cong k(M.C)$ onto the function field carrying $\operatorname{algebraMap}_{k,F}$ to the canonical map $k \to k(M.C)$, a bijection from the closed points of $M.C$ onto the set of places of $F/k$ (valuation subrings of $F$ containing the image of $k$, different from $F$, whose ideals are principal) under which the image of the stalk at a closed point inside $k(M.C)$, read back in $F$, is exactly the corresponding valuation subring, and the property that every finite subset of $M.C$ lies in some affine open. Let $\nu : M.C \to C$ be a morphism over $\operatorname{Spec} k$, i.e. $\nu$ followed by $c$ equals $M.toBase$, and assume the induced map of stalks at the generic point of $M.C$ is an isomorphism. Let $U$ be an open subscheme of $C$ which is affine and non-empty. Then the integral closure of $\Gamma(C,U)$ in the function field $k(C)$, taken with respect to the canonical germ map $\Gamma(C,U) \to k(C)$, is a finitely generated $\Gamma(C,U)$-module.
--
--   This is the finiteness of the normalisation of an affine chart of a proper integral curve which admits a birational morphism from a smooth proper model; classically it identifies the integral closure of the ring of sections with the ring of sections of the model over the preimage chart, a finite module. It feeds into [`AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen`](thm.html#AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_finite_integralClosure_sections_of_isIso_stalkMap.lean

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

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve

theorem AlgebraicCurve.CurveModel.finite_integralClosure_sections_of_isIso_stalkMap
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (U : C.Opens) (hUaff : IsAffineOpen U) [Nonempty U] :
    Module.Finite Γ(C, U) ↥(integralClosure Γ(C, U) C.functionField) := by sorry
