-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
-- name    : AlgebraicCurve.Place.ord_smul_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ade5b407-0841-5603-9f32-5eed766c44cb
-- title:
--   Order at a place is invariant under nonzero constants
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F/K$ in the sense of the project: a valuation subring `v.toValuationSubring` of $F$ that contains $\operatorname{algebraMap} K F\,(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring. For such a $v$, `v.adicValuation` denotes the $\mathbb{Z}^{m0}$-valued valuation on $F$ attached to the corresponding height-one prime of the valuation ring, and `v.ord f` is defined as $-\log$ of `v.adicValuation f`, an integer, with the convention arising from $\log$ on $\mathbb{Z}^{m0}$ that $\operatorname{ord}_v(0) = 0$. The theorem asserts: for every $c \in K$ with $c \neq 0$ and every $x \in F$, the scalar multiple $c \bullet x$ satisfies $\operatorname{ord}_v(c \bullet x) = \operatorname{ord}_v(x)$. Note that no hypothesis is placed on $x$; the case $x = 0$ is covered by the convention just described.
--
--   This is the statement that the normalised order function at a place of $F/K$ is constant on $K^\times$-orbits, i.e. that nonzero elements of the constant field are units of every place's valuation ring. It is used throughout the divisor-theoretic part of the development, for instance when computing orders of elements modified by a nonzero constant factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_smul_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by sorry
