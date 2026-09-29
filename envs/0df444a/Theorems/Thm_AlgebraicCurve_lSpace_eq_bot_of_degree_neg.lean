-- Prove2me | Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
-- name    : AlgebraicCurve.lSpace_eq_bot_of_degree_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/193c3207-9415-57ea-b35e-c8a7e63242ce
-- title:
--   L(D)=0 for divisors of negative degree
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $D$ be a divisor of $F/K$, that is, a finitely supported function from the set of places of $F/K$ to $\mathbb{Z}$; here a place is a valuation subring $\mathcal{O}_v \subsetneq F$ which contains the image of $K$ and is a principal ideal ring. Assume $F/K$ satisfies `IsCurveOver`: every nonzero $f \in F$ admits a divisor $P$ with $P(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg P = 0$; every residue field $\mathcal{O}_v/\mathfrak{m}_v$ is finite-dimensional over $K$; and $\Omega_{F/K}$ is free of rank $1$ over $F$. Assume further that $\deg D = \sum_v D(v)\,\deg v < 0$. Then the Riemann–Roch space `LSpace D`, the $K$-submodule of those $f \in F$ with $v(f) \le \exp(D(v))$ for all places $v$, is the zero submodule. Of the `IsCurveOver` data the proof uses only the existence of degree-zero principal divisors.
--
--   This is the standard first consequence of the degree formalism in the theory of function fields of one variable: a divisor of negative degree has trivial Riemann–Roch space. It underlies the computation of $\ell(D) = \dim_K L(D)$ and is invoked throughout the Riemann–Roch development, for instance in the finiteness and descent statements for Riemann–Roch spaces under reduction and constant field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem lSpace_eq_bot_of_degree_neg {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by sorry
