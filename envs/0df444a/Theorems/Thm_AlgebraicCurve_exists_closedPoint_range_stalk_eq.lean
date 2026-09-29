-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
-- name    : AlgebraicCurve.exists_closedPoint_range_stalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/6fb6cda9-84dd-55f7-b4fe-5023a0b8e40b
-- title:
--   Places of a proper smooth curve come from closed points
-- statement:
--   Let $K$ be a field and let $c : C \to \operatorname{Spec} K$ be a morphism of schemes with $C$ integral, $c$ proper and $c$ smooth of relative dimension $1$. Give the function field $C.\mathrm{functionField}$ (the stalk of $C$ at its generic point) the $K$-algebra structure coming from the ring homomorphism [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), namely the composite of the inverse of the global-sections comparison isomorphism for $\operatorname{Spec} K$, the map on global sections induced by $c$, and the germ map at the generic point. Then for every $v$ of type [`AlgebraicCurve.Place K C.functionField`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, every valuation subring $\mathcal{O}_v \subseteq K(C)$ such that $\mathcal{O}_v$ contains the image of $K$ under this structure map, $\mathcal{O}_v \neq K(C)$, and $\mathcal{O}_v$ is a principal ideal ring, there exists a point $x \in C$ such that the singleton $\{x\}$ is closed in $C$ and the range of the canonical ring homomorphism from the stalk $\mathcal{O}_{C,x}$ to $K(C)$ is exactly the underlying subring of $\mathcal{O}_v$.
--
--   This is the classical identification of the places of the function field of a proper smooth curve over $K$ with the local rings at its closed points, in the direction that every place is realised by a point; it is the existence half of the dictionary between places and points. It underlies the subsequent treatment of divisors and of sets of places on curves, being used for instance in the comparison of the places of a curve with those of a subcurve and in the statements about places lying over a given embedding.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.exists_closedPoint_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : AlgebraicCurve.Place K C.functionField, ∃ x : C, IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by sorry
