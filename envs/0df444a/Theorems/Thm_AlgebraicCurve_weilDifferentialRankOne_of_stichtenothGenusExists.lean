-- Prove2me | Theorems.Thm_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists
-- name    : AlgebraicCurve.weilDifferentialRankOne_of_stichtenothGenusExists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/da599423-5e50-54f2-b7a2-ce3b3cd829d1
-- title:
--   Weil differentials have rank one, given the Stichtenoth genus
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a divisor recording its orders at all places and of degree $0$, every place of $F$ over $K$ (a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring) has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank $1$ over $F$. Assume further `StichtenothGenusExists K F`: at least one place exists, the Riemann–Roch space $L(0)$ is finite-dimensional over $K$, and there are an integer $\gamma$ and a divisor $D_0$ (a finitely supported function from places to $\mathbb{Z}$) such that $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. The conclusion is `WeilDifferentialRankOne K F`: for every $\varphi$ in the module of Weil differentials — the supremum over divisors $D$ of the subspaces `omegaSpace D` inside the $K$-dual of the adele space $\bigsqcup_D$ `adeleBdd D` $\subseteq (\mathrm{Place}\ K\ F \to F)$ — with $\varphi \neq 0$, and every Weil differential $\mu$, there is a unique $f \in F$ with $\mu =$ `weilSmul K F f` $\varphi$, the dual of multiplication by $f$ on the adele space applied to $\varphi$.
--
--   This is the classical statement that the Weil differentials of a one-variable function field form a one-dimensional module over $F$ (Stichtenoth I.5.14), here derived from the existence of the maximum of $\deg D - \ell(D)$, which is the form of the genus used in the adelic approach to Riemann–Roch. It is consumed by [`AlgebraicCurve.weilDifferentialRankOne_of_isCurveOver`](thm.html#AlgebraicCurve.weilDifferentialRankOne_of_isCurveOver), where genus existence is obtained from the tower over a rational subfield.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem weilDifferentialRankOne_of_stichtenothGenusExists {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) : WeilDifferentialRankOne K F := by sorry
