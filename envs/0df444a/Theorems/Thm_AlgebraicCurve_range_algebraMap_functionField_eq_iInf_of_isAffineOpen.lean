-- Prove2me | Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
-- name    : AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/527453d1-1eb0-5b28-9b59-6673dc342324
-- title:
--   Affine sections as intersection of places centred in U
-- statement:
--   Let $K$ be a field, let $C$ be a scheme over the universe $u$ equipped with a morphism $c : C \to \operatorname{Spec} K$, assume $C$ integral and $c$ smooth of relative dimension $1$, and let $U$ be an open subscheme of $C$ which is an affine open and whose underlying set is nonempty. The function field $C.\mathrm{functionField}$, i.e. the stalk of $\mathcal{O}_C$ at the generic point of $C$, is made a $K$-algebra via [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the ring homomorphism obtained by composing the inverse of the canonical isomorphism $K \cong \Gamma(\operatorname{Spec} K, \mathcal{O})$, the map on global sections induced by $c$, and the germ map $\Gamma(C,\mathcal{O}_C) \to \mathcal{O}_{C,\eta}$ at the generic point. The assertion is an equality of subrings of the function field: the range of the algebra map $\Gamma(C, U) \to C.\mathrm{functionField}$ equals the infimum, taken over all $v$ of type [`AlgebraicCurve.Place K C.functionField`](def/AlgebraicCurve_DivisorClassGroup.html#L22) — that is, over all valuation subrings $\mathcal{O}_v$ of the function field which contain the image of $K$, are not the whole field, and are principal ideal rings — and over all proofs that there exists a point $x \in U$ with $\{x\}$ closed in $C$ and with the range of $\mathcal{O}_{C,x} \to C.\mathrm{functionField}$ equal to $\mathcal{O}_v$, of the underlying subring of $\mathcal{O}_v$. Thus the ring of sections over $U$ is the intersection of those $\mathcal{O}_v$ that are centred at a closed point of $U$.
--
--   This identifies the ring of regular functions on an affine chart of a smooth curve with a holomorphy ring: the intersection of the valuation rings of the places centred in that chart, the degree-zero analogue of a Riemann–Roch space $L_U(0)$. It is used in the comparison of the Čech complex of $\mathcal{O}_C$ for a cover by two affine opens with the function-field (répartition) description, and is cited in the construction of the divisor class group and in the finiteness statements for curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (algebraMap Γ(C, U) C.functionField).range =
      ⨅ (v : AlgebraicCurve.Place K C.functionField)
        (_ : ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
          (algebraMap (C.presheaf.stalk x) C.functionField).range =
            v.toValuationSubring.toSubring),
        v.toValuationSubring.toSubring := by sorry
