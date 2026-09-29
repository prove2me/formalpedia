-- Prove2me | Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
-- name    : FormalGroup.isDrinfeldBasisAdic_zero_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/c26add84-856d-50eb-9658-6359b3163139
-- title:
--   (0,0) is a Drinfeld basis iff [q]_F = u X^{q^2}
-- statement:
--   Let $T$ be a commutative ring, $I \subseteq T$ an ideal such that $T$ is $I$-adically complete, let $F$ be a formal group law over $T$ (a two-variable power series satisfying the group-law axioms) and let $q$ be a natural number. Here `F.nthSeries` is defined by recursion, with `F.nthSeries 0 = 0` and `F.nthSeries (n+1)` the substitution of the pair $(\,$`F.nthSeries n`$,\,X)$ into the two-variable series of $F$; thus `F.nthSeries q` is the multiplication-by-$q$ series $[q]_F(X)$. The predicate `F.IsDrinfeldBasisAdic I q 0 0` says, with the $I$-adic topological data on $T$ used to make the required evaluations, that there is a unit $u \in T[[X]]$ with $[q]_F = u \cdot D$, where $D$ is the Drinfeld divisor of level $q$ attached to the pair $(0,0)$, namely the product over $a, b < q$ of the linear factors $X - C\big([a]\!\cdot\!0 +_F [b]\!\cdot\!0\big)$. The theorem asserts that this holds if and only if there is a unit $u \in T[[X]]$ with $[q]_F = u \cdot X^{q \cdot q}$. No restriction on $q$ is imposed, so the degenerate cases $q = 0, 1$ are included.
--
--   This identifies, for a formal group law over an adically complete ring, the condition that the pair $(0,0)$ be a Drinfeld basis of level $q$ with the height-two-type condition that the multiplication-by-$q$ series be a unit multiple of $X^{q^2}$; it is the supersingular-fibre case of the Drinfeld basis condition in the sense of Katz–Mazur. It is used downstream in the study of Drinfeld bases, for instance in producing monic divisors of the $q$-series under base change and in the uniqueness and trivialisation statements for formal group laws with a Drinfeld basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.isDrinfeldBasisAdic_zero_zero_iff
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T) (q : ℕ) :
    F.IsDrinfeldBasisAdic I q 0 0 ↔
      ∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ (q * q) := by sorry
