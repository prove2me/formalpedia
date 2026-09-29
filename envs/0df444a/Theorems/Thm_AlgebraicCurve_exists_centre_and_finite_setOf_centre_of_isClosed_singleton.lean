-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton
-- name    : AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/c088b8fd-7f93-508c-a83e-84f691c80510
-- title:
--   Closed points of a proper curve have finitely many, at least one, centring place
-- statement:
--   Let $k$ be an algebraically closed field and let $C$ be an integral scheme equipped with a proper morphism $c : C \to \operatorname{Spec} k$; via [`AlgebraicCurve.baseToFunctionField`](def/AlgebraicCurve_CurveModel.html#L18), namely the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism with $c$ on global sections followed by the germ map at the generic point, the function field $F = C.\mathrm{functionField}$ is a $k$-algebra. Assume `IsCurveOver k F`: every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$; for every place $v$ of $F/k$ — that is, every valuation subring $\mathcal{O}_v \subsetneq F$ containing the image of $k$ and which is a principal ideal ring — the residue field of $\mathcal{O}_v$ is finite over $k$; and $\Omega_{F/k}$ is free of rank one over $F$. Let $z \in C$ be a point whose singleton is closed. Call a place $v$ centred at $z$ when, for every $s$ in the stalk $\mathcal{O}_{C,z}$, the adic valuation (attached to the maximal ideal of $\mathcal{O}_v$, with values in $\mathbb{Z}^{m0}$) of the image of $s$ in $F$ is $\le 1$, and is $< 1$ whenever $s$ lies in the maximal ideal of $\mathcal{O}_{C,z}$. The assertion is that at least one place of $F/k$ is centred at $z$, and that the set of places centred at $z$ is finite.
--
--   This is the classical statement that each closed point of a proper integral curve is the centre of at least one and of only finitely many places of its function field, the valuation-theoretic form of dominating a local ring by a discrete valuation ring together with the finiteness of the fibres of the normalisation map. It is used in the comparison of the arithmetic genus of $C$ with the genus of its function field and the number of its non-regular local rings, and in the finiteness of the set of points of $C$ with non-regular stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton.lean

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

theorem AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (z : C) (hz : IsClosed ({z} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (∃ v : Place k C.functionField, (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))) ∧
      {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))}.Finite := by sorry
