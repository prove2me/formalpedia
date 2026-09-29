-- Prove2me | Theorems.Thm_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul
-- name    : AlgebraicCurve.lSpaceOn_setOf_centre_eq_span_integralClosure_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/f363120c-886b-52ba-9490-ee7ea535496b
-- title:
--   Functions regular at all places centred at a closed point
-- statement:
--   Let $k$ be an algebraically closed field, $C$ a scheme with a morphism $c : C \to \operatorname{Spec} k$ such that $C$ is integral and $c$ is proper, and let $K =$ `C.functionField` be regarded as a $k$-algebra through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the ring map obtained from $c$ on global sections followed by the germ map at the generic point. Assume `IsCurveOver k K`: every nonzero $f \in K$ admits a finitely supported divisor whose value at each place $v$ is $\operatorname{ord}_v f$ and whose degree is $0$, every place of $K$ over $k$ has residue field finite over $k$, and $\Omega_{K/k}$ is free of rank $1$ over $K$. Assume further that every point of $C$ is either the generic point or closed. Let $U$ be a nonempty affine open of $C$ and $z \in U$ a closed point. Here a place is a valuation subring of $K$ containing the image of $k$, distinct from $K$, and a principal ideal ring. Then the $k$-subspace of $K$ consisting of those $f$ with $v(f) \le 1$ for every place $v$ such that every $s \in \mathcal{O}_{C,z}$ satisfies $v(s) \le 1$, with $v(s) < 1$ when $s$ lies in the maximal ideal of $\mathcal{O}_{C,z}$ (images taken in $K$), coincides with the $k$-span of the set of products $a b$ with $a$ in the integral closure of $\Gamma(C, U)$ in $K$ and $b$ in the image of $\mathcal{O}_{C,z} \to K$.
--
--   This identifies the holomorphy ring of the places centred at a closed point $z$ of a proper integral curve with the integral closure of the local ring $\mathcal{O}_{C,z}$, presented as the product of the integral closure of an affine chart containing $z$ with the image of the stalk. It is used in [`AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen`](thm.html#AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen), in the comparison of Čech data for divisors on the curve with local contributions at the singular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul.lean

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

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.lSpaceOn_setOf_centre_eq_span_integralClosure_mul
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C))
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U)
    (z : C) (hzU : z ∈ U) (hz : IsClosed ({z} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) =
      Submodule.span k ((integralClosure Γ(C, U) C.functionField : Set C.functionField) *
        Set.range (algebraMap (C.presheaf.stalk z) C.functionField)) := by sorry
