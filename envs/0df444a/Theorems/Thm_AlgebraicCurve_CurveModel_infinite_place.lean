-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
-- name    : AlgebraicCurve.CurveModel.infinite_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/3c260daf-c300-57e4-ae57-308165cb6398
-- title:
--   A function field with a smooth proper model has infinitely many places
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure, and suppose given a term $M$ of type `CurveModel K F`, that is: an integral scheme $C$ together with a morphism $C \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$; a ring isomorphism between $F$ and the function field of $C$ carrying $\operatorname{algebraMap} K F (a)$ to the image of $a$ under the canonical map $K \to C.\mathrm{functionField}$ induced by the structure morphism; a map from the closed points of $C$ to the type `Place K F` of places of $F$ over $K$ (valuation subrings of $F$ that contain the image of $K$, are proper subrings, and are principal ideal rings), which is bijective and which matches, at each closed point $x$, the image of the stalk at $x$ inside the function field, transported to $F$, with the valuation subring of the corresponding place; and the condition that every finite set of points of $C$ lies in a single affine open. The conclusion is that the type `Place K F` is infinite.
--
--   This is the classical statement that a one-variable function field over an algebraically closed constant field has infinitely many places, here for fields presented by a smooth proper integral model. It is invoked throughout the treatment of divisors and the relative Picard functor for such models, for instance in the construction of divisors supported away from a prescribed finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_infinite_place.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicGeometry
open AlgebraicCurve

theorem AlgebraicCurve.CurveModel.infinite_place
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) : Infinite (Place K F) := by sorry
