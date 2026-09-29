-- Prove2me | Theorems.Thm_AlgebraicCurve_lSpaceOn_setOf_exists_centre_eq_span_integralClosure
-- name    : AlgebraicCurve.lSpaceOn_setOf_exists_centre_eq_span_integralClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/3e13400e-debd-5b06-91dc-7b4587196a8b
-- title:
--   Holomorphy ring of an affine chart is the integral closure
-- statement:
--   Let $k$ be an algebraically closed field, $C$ an integral scheme and $c : C \to \operatorname{Spec} k$ a proper morphism; the function field $K =$ `C.functionField` is regarded as a $k$-algebra through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), namely the germ at the generic point of the map on global sections induced by $c$. Assume `IsCurveOver k K`: every nonzero $f \in K$ has a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$, each place $v$ of $K/k$ (a valuation subring of $K$ that contains the image of $k$, is not all of $K$, and is a principal ideal ring) has residue field finite over $k$, and $\Omega_{K/k}$ is free of rank one over $K$. Let $U \subseteq C$ be a nonempty affine open. Then the $k$-submodule of $f \in K$ with $v(f) \le 1$ for every place $v$ that is centred at some $z \in U$ — i.e. $v$ takes values $\le 1$ on the image of the stalk $\mathcal O_{C,z}$ in $K$ and values $< 1$ on the image of $\mathfrak m_z$ — coincides with the $k$-linear span of the integral closure of $\Gamma(C, U)$ in $K$.
--
--   This identifies the holomorphy ring of the set of places centred in an affine chart with the integral closure of the chart's coordinate ring, the classical description of an intersection of valuation rings as an integral closure, here in the form of an equality of $k$-subspaces of the function field. It is used in the analysis of Čech cohomology of divisors on a chart, via [`AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen`](thm.html#AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_lSpaceOn_setOf_exists_centre_eq_span_integralClosure.lean

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

theorem AlgebraicCurve.lSpaceOn_setOf_exists_centre_eq_span_integralClosure
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) =
      Submodule.span k (integralClosure Γ(C, U) C.functionField : Set C.functionField) := by sorry
