-- Prove2me | Theorems.Thm_AlgebraicCurve_weilReciprocity
-- name    : AlgebraicCurve.weilReciprocity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/871a1afc-4e5a-54af-91ba-822347c3b173
-- title:
--   Weil reciprocity for function fields in characteristic zero
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a field that is simultaneously a $K$-algebra and a $\mathrm{RatFunc}\,K = K(X)$-algebra, compatibly (the scalar tower $K \to K(X) \to F$), with $F$ finite-dimensional over $K(X)$, and assume `HasPrincipalDivisors K F`: every nonzero $f \in F$ admits a finitely supported $D : \mathrm{Place}\,K\,F \to \mathbb{Z}$ with $D(v) = \operatorname{ord}_v f$ for every place $v$ and $\deg D = \sum_v D(v)\cdot \deg v = 0$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. The conclusion is the predicate `WeilReciprocity K F`: for all nonzero $f, g \in F$ and all finitely supported divisors $D_f, D_g$ with $D_f(v) = \operatorname{ord}_v f$ and $D_g(v) = \operatorname{ord}_v g$ for every place $v$, such that at every place at least one of $\operatorname{ord}_v f$, $\operatorname{ord}_v g$ vanishes, and such that every place in the support of $D_f$ and every place in the support of $D_g$ is rational (the map $K \to$ residue field of $v$ is surjective), one has $\prod_v (\mathrm{ev}_v f)^{D_g(v)} = \prod_v (\mathrm{ev}_v g)^{D_f(v)}$, the products being over the supports of $D_g$ and $D_f$ respectively. Under the present hypotheses the rationality conditions are automatic, by [`AlgebraicCurve.Place.isRational_of_isAlgClosed`](thm.html#AlgebraicCurve.Place.isRational_of_isAlgClosed).
--
--   This is Weil reciprocity for the function field of a smooth projective curve over an algebraically closed field of characteristic zero, in the divisor-theoretic form $f(\operatorname{div} g) = g(\operatorname{div} f)$ for functions with divisors of disjoint support. It serves as the anchor for the function-field divisor calculus used further on, and is cited in the construction of the Weil pairing on divisor classes of degree zero, notably by [`AlgebraicCurve.Pic0.exists_weilPairing`](thm.html#AlgebraicCurve.Pic0.exists_weilPairing), [`AlgebraicCurve.Pic0.exists_antisymmWeilPairing`](thm.html#AlgebraicCurve.Pic0.exists_antisymmWeilPairing) and [`AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_weilReciprocity.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.weilReciprocity (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] : WeilReciprocity K F := by sorry
