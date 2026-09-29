-- Prove2me | Theorems.Thm_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
-- name    : AlgebraicCurve.isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/4a95ef94-271e-585c-ad43-60290adabb02
-- title:
--   Vanishing δ_z implies the local ring at z is regular
-- statement:
--   Let $k$ be an algebraically closed field, let $C$ be a scheme with a morphism $c : C \to \operatorname{Spec} k$ such that $C$ is integral and $c$ is proper, and let $z$ be a point of $C$; the function field $C.\text{functionField}$ (the stalk at the generic point) is regarded as a $k$-algebra through [`AlgebraicCurve.baseToFunctionField`](def/AlgebraicCurve_CurveModel.html#L18), which is the germ at the generic point of the map on global sections induced by $c$. Write $\varphi$ for the canonical map $\mathcal{O}_{C,z} \to C.\text{functionField}$ and let $S_z$ be the set of places $v$ of $C.\text{functionField}$ over $k$ — that is, valuation subrings of the function field that contain the image of $k$, are proper, and are principal ideal rings, equipped with the $\mathbb{Z}^{m0}$-valued valuation of their height-one maximal ideal — which are centred at $z$ in the sense that $v(\varphi s) \le 1$ for every $s \in \mathcal{O}_{C,z}$ and $v(\varphi s) < 1$ for every $s$ in the maximal ideal of $\mathcal{O}_{C,z}$. Assume (i) $S_z$ is finite, and (ii) $\mathrm{lSpaceOn}\,S_z\,0 = \{f : v(f) \le 1 \text{ for all } v \in S_z\}$, the intersection of the valuation rings of the places centred at $z$, is contained in the image of $\varphi$. Then $\mathcal{O}_{C,z}$ is a regular local ring.
--
--   This is the implication $\delta_z = 0 \Rightarrow \mathcal{O}_{C,z}$ regular for a point of a proper integral curve over an algebraically closed field, where $\delta_z$ measures the failure of the local ring to be the full intersection of the valuation rings centred at $z$. It is used in the place-theoretic route to the inequality between the arithmetic genus, the genus of the function field and the number of singular points, and in the statement that a morphism of integral schemes which is an isomorphism on stalks away from finitely many points has only finitely many non-regular stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range.lean

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

theorem AlgebraicCurve.isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (z : C)
    (hSfin : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra;
      {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))}.Finite)
    (hδ : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra;
      ((lSpaceOn {v : Place k C.functionField |
        (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) : Set C.functionField) ⊆
        Set.range (algebraMap (C.presheaf.stalk z) C.functionField))) :
    IsRegularLocalRing (C.presheaf.stalk z) := by sorry
