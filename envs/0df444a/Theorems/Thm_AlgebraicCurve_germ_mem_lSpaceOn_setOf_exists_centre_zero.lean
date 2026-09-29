-- Prove2me | Theorems.Thm_AlgebraicCurve_germ_mem_lSpaceOn_setOf_exists_centre_zero
-- name    : AlgebraicCurve.germ_mem_lSpaceOn_setOf_exists_centre_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/8245f5a4-11bb-5947-aadb-d0790afee36f
-- title:
--   Sections over U lie in L_{S_U}(0)
-- statement:
--   Let $k$ be an algebraically closed field, let $C$ be an integral scheme over $k$ by way of a morphism $c : C \to \operatorname{Spec} k$ that is proper, let $U$ be an open subscheme of $C$ containing the generic point $\eta$ of $C$, and let $t \in \Gamma(C, U)$. The function field $C.\mathrm{functionField}$ is regarded as a $k$-algebra through the ring homomorphism [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $k$, the map on global sections induced by $c$, and the germ at $\eta$ of the global sections. Here a place of $C.\mathrm{functionField}$ over $k$ is a valuation subring of the function field that contains the image of $k$, is not the whole field, and is a principal ideal ring, and its associated valuation is the $\mathbb{Z}^{m0}$-valued valuation attached to the maximal ideal of that subring. Let $S_U$ be the set of places $v$ for which there exists $z \in U$ such that every $s$ in the stalk $\mathcal{O}_{C,z}$ has image in the function field of valuation $\le 1$ under $v$, and of valuation $< 1$ whenever $s$ lies in the maximal ideal of $\mathcal{O}_{C,z}$; that is, $v$ is centred at $z$. The assertion is that the germ of $t$ at $\eta$ lies in the space `lSpaceOn` $S_U$ applied to the zero divisor, i.e. that $v(t_\eta) \le 1$ for every $v \in S_U$.
--
--   This is the statement that a section of the structure sheaf over an open set $U$ is holomorphic (integral) at every place of the function field whose centre lies in $U$, the elementary inclusion of sheaf sections into the place-theoretic Riemann–Roch space $L_{S_U}(0)$. It feeds the comparison of the Čech complex of $\mathcal{O}_C$ on a two-chart cover with the place-theoretic Čech complex used in [`AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing`](thm.html#AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_germ_mem_lSpaceOn_setOf_exists_centre_zero.lean

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

theorem AlgebraicCurve.germ_mem_lSpaceOn_setOf_exists_centre_zero
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (U : C.Opens) (hU : genericPoint C ∈ U) (t : Γ(C, U)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    C.presheaf.germ U (genericPoint C) hU t ∈
      lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧
        (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) := by sorry
