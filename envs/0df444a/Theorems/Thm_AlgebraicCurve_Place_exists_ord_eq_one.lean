-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
-- name    : AlgebraicCurve.Place.exists_ord_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c53dc47f-3d74-56f4-b027-ea46543b40cc
-- title:
--   Existence of a uniformiser at a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring $\mathcal{O}_v \subseteq F$ which contains $\operatorname{algebraMap} K F (a)$ for every $a \in K$, which is not all of $F$, and which is a principal ideal ring. For $f \in F$ the integer $v.\mathrm{ord}\, f$ is defined as $-\log$ of the value $v.\mathrm{adicValuation}\, f \in \mathbb{Z}^{m0}$, where $v.\mathrm{adicValuation}$ is the valuation on $F$ attached to the height-one prime of $\mathcal{O}_v$ associated with $v$; thus $\mathrm{ord}$ is the normalised additive valuation of $v$, with $\mathrm{ord}\,0$ taking the value coming from $\log 0$. The assertion is that there exists $t \in F$ with $v.\mathrm{ord}\, t = 1$, i.e. that the normalised order function at $v$ attains the value $1$, so that a uniformiser at $v$ exists in $F$.
--
--   This is the existence of a prime element (uniformiser) at a place, the elementary starting point for local expansions at $v$; the value group of $\mathrm{ord}$ is thereby all of $\mathbb{Z}$. It is used throughout the development of divisors and differentials on a curve, for instance in the lemmas relating $\mathrm{ord}$ to differential coefficients and to non-vanishing of the derivation $D$ at $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_ord_eq_one.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ t : F, v.ord t = 1 := by sorry
