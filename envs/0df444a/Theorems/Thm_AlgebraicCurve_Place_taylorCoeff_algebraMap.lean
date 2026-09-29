-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
-- name    : AlgebraicCurve.Place.taylorCoeff_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/c9386c79-72f7-5e4b-a75b-7d63e2946caf
-- title:
--   Taylor coefficients of a constant at a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ which contains $\mathrm{image}(K\to F)$, is not all of $F$, and is a principal ideal ring. Let $t\in F$, let $c\in K$ and let $n$ be a natural number. Recall that the Taylor remainders of $f\in F$ at $v$ along $t$ are defined by $R_0(f)=f$ and $R_{r+1}(f)=\bigl(R_r(f)-\mathrm{algebraMap}_{K,F}(\mathrm{evalAt}_v(R_r(f)))\bigr)t^{-1}$, where $\mathrm{evalAt}_v(g)\in K$ is obtained, for $g$ in the valuation subring, by applying `residueInv` to the residue class of $g$ in the residue field, and is $0$ for $g$ outside the valuation subring; the $r$-th Taylor coefficient is $\mathrm{taylorCoeff}\,v\,t\,r\,f=\mathrm{evalAt}_v(R_r(f))$. The theorem asserts that the $n$-th Taylor coefficient along $t$ of the constant $\mathrm{algebraMap}_{K,F}(c)$ equals $c$ if $n=0$ and $0$ otherwise. No hypothesis is imposed on $t$ (it need not be a uniformiser at $v$).
--
--   This is the statement that the formal Taylor expansion at $v$ of a constant function is the constant power series, one of the compatibilities (alongside additivity and the product rule) that make $f\mapsto\sum_n \mathrm{taylorCoeff}\,v\,t\,n\,f\,T^n$ a $K$-algebra map on the functions regular at $v$. It is used in the development of Taylor expansions at a place, for instance in the identification of the expansion of polynomial expressions and in the results on inverses and on expansions of the form $C+X$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.taylorCoeff_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t : F) (c : K) (n : ℕ) :
    taylorCoeff v t n (algebraMap K F c) = if n = 0 then c else 0 := by sorry
