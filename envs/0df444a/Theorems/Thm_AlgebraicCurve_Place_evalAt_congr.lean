-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
-- name    : AlgebraicCurve.Place.evalAt_congr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/3a35d3f2-9ecf-570d-a8df-cf65818da0f0
-- title:
--   Values at a place agree for functions congruent modulo mathfrak mᵥ
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Let $f, g \in F$ be elements of $\mathcal O_v$, and suppose that either $f - g = 0$ or $0 < \operatorname{ord}_v(f-g)$, where $\operatorname{ord}_v(x) = -\log\bigl(\mathrm{v.adicValuation}(x)\bigr)$ is minus the $\mathbb Z^{m0}$-logarithm of the valuation of the height-one prime attached to $v$. Then $\mathrm{v.evalAt}\,f = \mathrm{v.evalAt}\,g$, where for $x \in \mathcal O_v$ the value $\mathrm{v.evalAt}\,x \in K$ is obtained by taking the residue of $x$ in the residue field of $\mathcal O_v$ and applying `v.residueInv`, a fixed left inverse (chosen via `Function.invFun`) of the structure map $K \to \mathcal O_v/\mathfrak m_v$, and $\mathrm{v.evalAt}\,x = 0$ for $x \notin \mathcal O_v$. The separate disjunct $f-g=0$ is needed because $\operatorname{ord}_v 0 = 0$ with the conventions in force.
--
--   This is the congruence property of evaluation at a place: functions regular at $v$ and congruent modulo the maximal ideal have the same value at $v$. It is the bridge between the abstract residue-field definition of $f(v)$ and concrete formulae for values, and is used throughout the function-field layer, for instance in computing values at the places of a rational function field, including the place at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_congr.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_congr {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (h : f - g = 0 ∨ 0 < v.ord (f - g)) : v.evalAt f = v.evalAt g := by sorry
