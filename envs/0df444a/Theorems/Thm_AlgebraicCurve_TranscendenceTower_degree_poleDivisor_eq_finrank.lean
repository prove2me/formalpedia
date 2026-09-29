-- Prove2me | Theorems.Thm_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank
-- name    : AlgebraicCurve.TranscendenceTower.degree_poleDivisor_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/ca060c2f-1709-5915-8b0f-48f771e7e8e3
-- title:
--   Degree of the pulled-back pole divisor equals [F:E]
-- statement:
--   Let $K$, $E$, $F$ be fields with $K$-algebra structures on $E$ and $F$ and an $E$-algebra structure on $F$ forming a scalar tower over $K$, with $F/E$ finite-dimensional and separable, and assume $F$ has principal divisors over $K$: every nonzero $f \in F$ is the divisor of some $D$, meaning $D(v) = \operatorname{ord}_v f$ at every place $v$ of $F/K$ and $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, whose ring is a principal ideal ring, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, and $\deg D = \sum_v D(v)\,\deg v$. Let $T$ be transcendence-tower data for $K \subseteq E \subseteq F$, that is: an element $x \in E$ whose powers $x^j$ ($j \in \mathbb{N}$) are linearly independent over $K$, together with a place $v$ of $E/K$ with $\deg v = 1$, $\operatorname{ord}_v x = -1$, and $\operatorname{ord}_u x \ge 0$ for every place $u \neq v$ of $E/K$. The assertion is that the degree of the pole divisor of $T$, namely the image under `Divisor.pullback` to $F$ of the divisor $1 \cdot v$ on $E$, equals $\operatorname{finrank}_E F = [F:E]$ as an integer.
--
--   This is the identity $\deg (x)_\infty = [F:K(x)]$ for a function field: the fundamental identity $\sum_{w \mid v} e(w\mid v) f(w\mid v) = [F:E]$, specialised to a degree-one place $v$ of $E$ at which $x$ has a simple pole. It supplies the identification of the extension degree with the degree of the pole divisor used in the pole-divisor package, and is cited in the estimate [`AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable`](thm.html#AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean

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

theorem TranscendenceTower.degree_poleDivisor_eq_finrank {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] (T : TranscendenceTower K E F) :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by sorry
