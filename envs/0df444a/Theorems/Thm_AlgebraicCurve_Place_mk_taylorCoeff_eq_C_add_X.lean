-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X
-- name    : AlgebraicCurve.Place.mk_taylorCoeff_eq_C_add_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6cd85594-d767-5ca6-8e51-8ae73330a86a
-- title:
--   Taylor expansion of z in the parameter z-z(v) is z(v)+T
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project, i.e. a valuation subring $\mathcal O_v = v.\mathtt{toValuationSubring}$ of $F$ which contains $\mathrm{algebraMap}\,K\,F(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring. Write $\mathrm{res}_v$ for the residue map of $\mathcal O_v$, and for $f \in F$ let $v.\mathtt{evalAt}\,f \in K$ be the value of $f$ at $v$: it is $v.\mathtt{residueInv}(\mathrm{res}_v f)$, the image of $\mathrm{res}_v f$ under a chosen left inverse (`Function.invFun`) of $\mathrm{algebraMap}\,K\,(\mathcal O_v/\mathfrak m_v)$, when $f \in \mathcal O_v$, and $0$ otherwise. Assume $v$ is rational, i.e. $\mathrm{algebraMap}\,K\,(\mathcal O_v/\mathfrak m_v)$ is surjective, let $z \in \mathcal O_v$, and put $t = z - \mathrm{algebraMap}\,K\,F(v.\mathtt{evalAt}\,z)$; assume $v.\mathtt{ord}\,t = 1$, where $v.\mathtt{ord}$ is minus the logarithm of the adic valuation attached to the height-one prime of $\mathcal O_v$. The Taylor remainders along $t$ are defined by $R_0(f) = f$ and $R_{r+1}(f) = (R_r(f) - \mathrm{algebraMap}\,K\,F(v.\mathtt{evalAt}\,R_r(f)))\,t^{-1}$, and the coefficients by $v.\mathtt{taylorCoeff}\,t\,r\,f = v.\mathtt{evalAt}\,R_r(f)$. The conclusion is the identity of formal power series $\sum_{n \ge 0} (v.\mathtt{taylorCoeff}\,t\,n\,z)\,T^n = v.\mathtt{evalAt}\,z + T$ in $K[[T]]$, written with `PowerSeries.mk`, `PowerSeries.C` and `PowerSeries.X`. The proof uses neither the rationality hypothesis on $v$ nor the membership $z \in \mathcal O_v$.
--
--   This is the normalisation statement that in the local chart at $v$ given by the parameter $t = z - z(v)$, the function $z$ itself expands as $z(v) + T$; it fixes the shape of local parameters of the form $x - x(v)$. It feeds the computations of power-series expansions of functions at a place, in particular [`AlgebraicCurve.Place.mk_taylorCoeff_aeval`](thm.html#AlgebraicCurve.Place.mk_taylorCoeff_aeval) and [`AlgebraicCurve.Place.evalEval_C_add_X_mk_taylorCoeff_eq_zero`](thm.html#AlgebraicCurve.Place.evalEval_C_add_X_mk_taylorCoeff_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mk_taylorCoeff_eq_C_add_X.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.mk_taylorCoeff_eq_C_add_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z : F} (hz : z ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1) :
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n z)
      = PowerSeries.C (v.evalAt z) + PowerSeries.X := by sorry
