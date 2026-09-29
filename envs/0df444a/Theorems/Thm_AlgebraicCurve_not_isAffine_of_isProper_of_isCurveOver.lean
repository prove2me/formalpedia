-- Prove2me | Theorems.Thm_AlgebraicCurve_not_isAffine_of_isProper_of_isCurveOver
-- name    : AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/618366c3-7150-5623-9b12-52b63e53a8c1
-- title:
--   Properness and a curve function field preclude affineness
-- statement:
--   Let $k$ be an algebraically closed field and let $C$ be a scheme together with a morphism $c : C \to \operatorname{Spec} k$, where $C$ is integral and $c$ is proper. Regard the function field $\Gamma$ of $C$ (the stalk of $\mathcal{O}_C$ at the generic point) as a $k$-algebra via [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), namely the ring homomorphism $k \to \Gamma(C,\top) \to C.\mathrm{functionField}$ obtained from the global-sections map of $c$, identified with $k$ through $\Gamma(\operatorname{Spec} k, \mathcal{O})\cong k$, followed by the germ map at the generic point. Assume that for this algebra structure the predicate `IsCurveOver k C.functionField` holds; that is: every nonzero $f$ in the function field admits a divisor $D$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and $\deg D = 0$, where a place is a valuation subring of the function field which contains the image of $k$, is not the whole field and is a principal ideal ring; the residue field of every such place is a finite $k$-module; and the module of Kähler differentials $\Omega_{C.\mathrm{functionField}/k}$ is free of rank $1$ over the function field. The conclusion is that $C$ is not affine.
--
--   This is the statement that a complete (here proper) integral scheme over an algebraically closed field whose function field is a one-variable function field has positive dimension and therefore cannot be affine. It is used in the place-theoretic part of the development, both in the construction of centres of places on such a scheme and in the Euler-characteristic bound relating the arithmetic genus, the genus of the function field and the number of non-regular local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_not_isAffine_of_isProper_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField) :
    ¬ IsAffine C := by sorry
