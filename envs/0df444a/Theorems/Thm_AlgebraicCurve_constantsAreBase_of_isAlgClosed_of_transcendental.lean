-- Prove2me | Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
-- name    : AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/d7f11e84-74c2-50a3-a08a-692ae5afaed9
-- title:
--   Constants are the base field when K is algebraically closed
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure. Suppose given $x \in F$ transcendental over $K$ such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Then `ConstantsAreBase K F` holds: writing `Divisor K F` for the group of finitely supported $\mathbb{Z}$-valued functions on the set `Place K F` of places of $F$ over $K$, and `LSpace D` for the Riemann–Roch space `riemannRochSpace D` viewed as a $K$-submodule of $F$, the assertion is the equality of $K$-submodules of $F$
--   $$\mathcal{L}(0) \;=\; \operatorname{range}\big(\mathrm{Algebra.linearMap}\ K\ F\big),$$
--   that is, the Riemann–Roch space of the zero divisor coincides with the image of $K$ in $F$ under the structure map. Thus the only elements of $F$ that are regular at every place of $F/K$ are the images of the elements of $K$.
--
--   This is the classical statement that the field of constants of a function field of one variable over an algebraically closed base field is the base field itself (Stichtenoth, Cor. I.1.20). It feeds the Riemann–Roch package of the development, where it yields $\ell(0) = 1$, and is used in the treatment of the degree-zero divisor class group and of reduction of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ConstantsAreBase K F := by sorry
