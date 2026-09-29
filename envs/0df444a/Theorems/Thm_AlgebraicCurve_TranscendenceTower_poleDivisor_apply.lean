-- Prove2me | Theorems.Thm_AlgebraicCurve_TranscendenceTower_poleDivisor_apply
-- name    : AlgebraicCurve.TranscendenceTower.poleDivisor_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/c8adb414-3cbb-5da7-8b25-9073698e14c2
-- title:
--   Coefficients of the pole divisor π^*(v)
-- statement:
--   Let $K \subseteq E \subseteq F$ be fields forming a scalar tower over $K$, with $F/E$ separable, and assume `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ admits a divisor on $F$ of degree $0$ whose coefficient at each place is the order $\mathrm{ord}(f)$ at that place. Let $T$ be transcendence-tower data for $K, E, F$: an element $x \in E$ whose powers $x^j$ ($j \in \mathbb{N}$) are linearly independent over $K$, together with a place $v$ of $E$ over $K$ (a valuation subring of $E$ containing $\mathrm{algebraMap}\,K\,E$, distinct from $E$ itself and a principal ideal ring) with $\deg v = 1$, $\mathrm{ord}_v(x) = -1$, and $\mathrm{ord}_u(x) \ge 0$ for every place $u \neq v$ of $E$ over $K$. Then for every place $w$ of $F$ over $K$, the coefficient at $w$ of the pole divisor $T.\mathrm{poleDivisor} =$ `Divisor.pullback F (Finsupp.single T.v 1)` equals the ramification index of $w$ over $E$ — the least $n > 0$ for which some nonzero $f \in E$ has $w(\mathrm{algebraMap}\,E\,F\,f) = n$ — multiplied by the value at the restricted place $w|_E$ (the contraction of the valuation subring of $w$ along $E \to F$) of the finitely supported function $\mathrm{single}\,(T.v)\,1$; that is, it is $e(w \mid T.v)$ when $w|_E = T.v$ and $0$ otherwise.
--
--   This is the pointwise description of the pullback to $F$ of a single place of $E$, in the case of the place $v$ of the transcendence-tower data, so that the pole divisor of $x$ viewed on $F$ is $\sum_{w \mid v} e(w\mid v)\, w$. It is used in the estimates on $\sum_w \mathrm{ord}$-differences bounding twice the genus of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TranscendenceTower_poleDivisor_apply.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem TranscendenceTower.poleDivisor_apply {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] (T : TranscendenceTower K E F) (w : Place K F) :
    T.poleDivisor w = (w.ramificationIndex E : ℤ) * (Finsupp.single T.v 1) (w.restrict E) := by sorry
