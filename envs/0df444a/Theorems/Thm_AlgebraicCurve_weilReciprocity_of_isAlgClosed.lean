-- Prove2me | Theorems.Thm_AlgebraicCurve_weilReciprocity_of_isAlgClosed
-- name    : AlgebraicCurve.weilReciprocity_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/75be8e30-fd22-5ca6-b7d5-026b56530ef1
-- title:
--   Weil reciprocity over an algebraically closed constant field
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with $K$-algebra and $\mathrm{RatFunc}\,K$-algebra structures forming a scalar tower over $K$, with $F$ finite-dimensional over the rational function field $\mathrm{RatFunc}\,K$, and assume `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ admits a finitely supported $\mathbb{Z}$-valued function $D$ on the places of $F$ over $K$ with $D(v) = \operatorname{ord}_v f$ for every place $v$ and $\deg D = 0$. Here a place is a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F$ of all of $K$, different from $F$ itself, and a principal ideal ring. The conclusion is `WeilReciprocity K F`: for all nonzero $f, g \in F$ and all divisors $D_f, D_g$ (finitely supported $\mathbb{Z}$-valued functions on places) such that $D_f(v) = \operatorname{ord}_v f$ and $D_g(v) = \operatorname{ord}_v g$ at every place $v$, such that at every place at least one of $\operatorname{ord}_v f$, $\operatorname{ord}_v g$ vanishes, and such that every place in the support of $D_f$ and every place in the support of $D_g$ is rational (the map $K \to$ residue field of $v$ is surjective), one has $\prod_v (\mathrm{evalAt}_v f)^{D_g(v)} = \prod_v (\mathrm{evalAt}_v g)^{D_f(v)}$, the products being taken over the supports. This is the form of [`AlgebraicCurve.weilReciprocity`](thm.html#AlgebraicCurve.weilReciprocity) with the hypothesis $\operatorname{char} K = 0$ removed.
--
--   This is Weil reciprocity for the function field of a curve over an algebraically closed constant field, in arbitrary characteristic: the evaluation of $f$ on the divisor of $g$ agrees with that of $g$ on the divisor of $f$ when the two divisors have disjoint supports. It is used in the construction and injectivity arguments for the divisorial Weil pairing on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_weilReciprocity_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.weilReciprocity_of_isAlgClosed (K F : Type*) [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] : WeilReciprocity K F := by sorry
