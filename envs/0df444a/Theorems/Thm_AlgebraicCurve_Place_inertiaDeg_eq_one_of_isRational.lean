-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
-- name    : AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/74ea38dc-0f13-5166-b3d5-220e06590201
-- title:
--   Rational place over a rational place has inertia degree one
-- statement:
--   Let $K \subseteq F \subseteq F'$ be a tower of fields, with $F$ and $F'$ algebras over $K$, $F'$ an algebra over $F$ compatibly with the $K$-structures, and $F'$ integral over $F$. Let $w$ be a place of $F'$ over $K$, i.e. a valuation subring of $F'$ that contains the image of $K$, is not the whole of $F'$, and is a principal ideal ring. Its restriction `w.restrict F` is the place of $F$ over $K$ given by the preimage of that valuation subring under the structure map $F \to F'$. Assume $w$ is rational, meaning that the map from $K$ to the residue field of the valuation subring of $w$ is surjective, and likewise that `w.restrict F` is rational, i.e. $K$ surjects onto the residue field of its valuation subring. The conclusion is that the inertia degree `w.inertiaDeg F`, defined as the rank of the residue field of $w$ as a module over the residue field of `w.restrict F`, equals $1$.
--
--   This is the degenerate case of the multiplicativity of degrees in a tower of places, $\deg w = \deg (w|_F)\cdot f(w \mid w|_F)$: when the residue fields at both levels coincide with the constant field $K$, the relative residue (inertia) degree is trivial. It is used throughout the divisor formalism for places of function fields, for instance in the comparison of push-forward and evaluation of divisors and in the computations with the divisorial Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) (hv : (w.restrict F).IsRational) : w.inertiaDeg F = 1 := by sorry
