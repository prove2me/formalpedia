-- Prove2me | Theorems.Thm_AlgebraicCurve_existsUnique_centre_place_of_isProper
-- name    : AlgebraicCurve.existsUnique_centre_place_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e2b70211-8759-5676-8ee9-f28434155888
-- title:
--   Unique centre on a proper curve for each place
-- statement:
--   Let $k$ be an algebraically closed field and let $c : C \to \operatorname{Spec} k$ be a morphism of schemes with $C$ integral and $c$ proper. The function field $C.\mathrm{functionField}$ (the stalk at the generic point) is regarded as a $k$-algebra via [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), namely the composite of the inverse of the canonical isomorphism $k \cong \Gamma(\operatorname{Spec} k)$, the map $c^{\sharp}$ on global sections, and the germ at the generic point. It is assumed that, for this algebra structure, $C.\mathrm{functionField}$ is a curve over $k$ in the sense of `IsCurveOver`: principal divisors exist (every nonzero $f$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$), the residue field of every place is a finite $k$-module, and $\Omega_{F/k}$ is free of rank one over $F = C.\mathrm{functionField}$. Here a place of $F$ over $k$ is a valuation subring $\mathcal{O}_v \subsetneq F$ containing the image of $k$ and which is a principal ideal ring, and $v.\mathrm{adicValuation}$ is the associated $\mathbb{Z}^{m0}$-valued adic valuation attached to its maximal ideal. The conclusion is that for every such place $v$ there is exactly one point $z \in C$ with the property that for all $s$ in the local ring $\mathcal{O}_{C,z}$ the image of $s$ in $F$ has $v.\mathrm{adicValuation} \le 1$, and has $v.\mathrm{adicValuation} < 1$ whenever $s$ lies in the maximal ideal of $\mathcal{O}_{C,z}$.
--
--   This is the existence and uniqueness of the centre on $C$ of a place of its function field: the unique point $z$ with $\mathcal{O}_{C,z} \subseteq \mathcal{O}_v$ and $\mathfrak{m}_z \subseteq \mathfrak{m}_v$. It supports the comparison of places with points of a possibly singular proper model, and is used in the estimate [`AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing`](thm.html#AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_existsUnique_centre_place_of_isProper.lean

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

theorem AlgebraicCurve.existsUnique_centre_place_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : Place k C.functionField, ∃! z : C, (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1)) := by sorry
