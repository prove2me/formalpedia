-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero
-- name    : AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/0c5fd925-9073-5211-9d64-0c4fdf858df4
-- title:
--   dt≠ 0 for t of nonzero order at a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra and $K$ of characteristic zero, and let $x\in F$ be an element such that $F$ is algebraic over the intermediate field $K(x)=\,$`IntermediateField.adjoin K {x}` (this is imposed as a typeclass hypothesis; $x$ itself is not assumed transcendental, so the hypothesis says that $F$ has transcendence degree at most one over $K$). Let $v$ be a place of $F$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place K F`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F$ which contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring; write $v.\mathrm{ord}$ for the associated order function on $F$ supplied by the project. Finally let $t\in F$ satisfy $v.\mathrm{ord}\,t\neq 0$ — for instance a uniformiser at $v$, or any element with a zero or pole there. The conclusion is that the image of $t$ under the universal derivation, $D_{K,F}(t)\in\Omega_{F/K}$ (Mathlib's `KaehlerDifferential.D K F`), is nonzero, i.e. $t$ is a separating element of $F/K$.
--
--   This is the standard fact that, over a base field of characteristic zero, any element with nonzero order at a place of a function field of one variable is separating, so that $dt$ spans the one-dimensional space of differentials. It underlies the project's order function on differentials, being used for the computation of `ordDiff` of $D$ of a uniformiser and of its behaviour under a constant field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    KaehlerDifferential.D K F t ≠ 0 := by sorry
