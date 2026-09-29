-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
-- name    : AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/a1d8c5f0-590a-5a6e-84a1-76247e1c2b07
-- title:
--   Order of df at a place, tame case
-- statement:
--   Let $K$ be a perfect field and $F$ a field equipped with a $K$-algebra structure, and suppose there is an element $x \in F$ such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$ in the sense of this development: a valuation subring of $F$ that contains $\operatorname{im}(K \to F)$, is not all of $F$, and is a principal ideal ring; for $g \in F$ write $v.\mathrm{ord}(g)$ for the associated normalised additive valuation, namely minus the logarithm of the value of $g$ under the valuation attached to the height-one prime of $v$. Let $f \in F$ and $c \in K$, and set $r = v.\mathrm{ord}(f - c)$, where $c$ is read in $F$ via the structure map. Assume $r \neq 0$ and that the image in $K$ of the natural number $|r|$ is nonzero, i.e. the characteristic of $K$ does not divide $|r|$. Then the order at $v$ of the Kähler differential $\mathrm{d}f \in \Omega_{F/K}$ equals $r - 1$. Here the order of a differential $\omega$ is computed as $v.\mathrm{ord}(g)$ for the coefficient $g$ with $\omega = g \cdot \mathrm{d}t$, $t$ a chosen element with $v.\mathrm{ord}(t) = 1$.
--
--   This is the computation of the order of a differential $\mathrm{d}f$ at a place in terms of the order of $f - c$, valid whenever that order is prime to the characteristic; it is the tame counterpart of the corresponding statement in characteristic zero, and without the tameness hypothesis only the inequality $\mathrm{ord}_v(\mathrm{d}f) \ge \mathrm{ord}_v(f - c) - 1$ survives. It is used in the analysis of places of modular curves, where orders of differentials encode ramification indices over the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve

theorem AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {f : F} {c : K}
    (hfc : v.ord (f - algebraMap K F c) ≠ 0)
    (htame : (((v.ord (f - algebraMap K F c)).natAbs : ℕ) : K) ≠ 0) :
    v.ordDiff (KaehlerDifferential.D K F f) = v.ord (f - algebraMap K F c) - 1 := by sorry
