-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_support_pullback_subset
-- name    : AlgebraicCurve.Divisor.support_pullback_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/84495a5c-585a-5f4b-968b-20c91b6a7f3b
-- title:
--   Support of a pulled-back divisor lies over its support
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, compatibly (scalar tower), with $F'$ integral over $F$; assume moreover that $F'/K$ has principal divisors, i.e. every $f \in F'$ with $f \neq 0$ admits a divisor $D$ of $F'/K$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ of $F'/K$ and $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$. For a divisor $E$ of $F/K$, the pull-back $\mathrm{pullback}\,E$ is the divisor of $F'/K$ obtained by additive extension of $v \mapsto \sum_{w \in \mathrm{fiber}(v)} E(v)\, e(w/F)\, w$, the sum over the finite set of places $w$ of $F'/K$ restricting to $v$, weighted by ramification indices. The assertion is the inclusion of finite sets $\mathrm{supp}(\mathrm{pullback}\,E) \subseteq \bigcup_{v \in \mathrm{supp}\,E} \mathrm{fiber}(v)$.
--
--   This is the elementary support bookkeeping for the conorm, or pull-back, of a divisor along $F \subseteq F'$: no place outside the fibres over $\mathrm{supp}\,E$ can occur in $\mathrm{pullback}\,E$. It is used to rewrite the evaluation of a function at a pulled-back divisor as a product over fibres, in [`AlgebraicCurve.Divisor.evalFun_pullback`](thm.html#AlgebraicCurve.Divisor.evalFun_pullback) and [`AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable`](thm.html#AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_support_pullback_subset.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.support_pullback_subset {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')] (E : Divisor K F) : (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') := by sorry
