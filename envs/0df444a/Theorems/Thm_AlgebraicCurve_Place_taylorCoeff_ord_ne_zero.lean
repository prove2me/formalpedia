-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_ord_ne_zero
-- name    : AlgebraicCurve.Place.taylorCoeff_ord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/83ef1366-b22a-5144-8619-d8433a6ff0c0
-- title:
--   Non-vanishing of the leading Taylor coefficient at a place
-- statement:
--   Let $K\subseteq F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal O_v=v.\mathtt{toValuationSubring}$ of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. Write $\operatorname{ord}_v$ for the associated order function, $\operatorname{ord}_v g=-\log$ of the value of the adic valuation of $\mathcal O_v$ at $g$, with values in $\mathbb Z$. Assume $v$ is rational, meaning that the structure map $K\to\mathcal O_v/\mathfrak m_v$ to the residue field is surjective; let $t\in F$ satisfy $\operatorname{ord}_v t=1$, and let $f\in\mathcal O_v$ be nonzero. Recall that the remainders are defined by $R_0=f$ and $R_{r+1}=(R_r-\iota(\mathrm{ev}_v(R_r)))t^{-1}$, where $\mathrm{ev}_v(g)\in K$ is the preimage in $K$ of the residue class of $g$ when $g\in\mathcal O_v$ and $0$ otherwise, and $\iota:K\to F$; the $r$-th Taylor coefficient of $f$ along $t$ is $\mathrm{ev}_v(R_r)\in K$. The conclusion is that the Taylor coefficient of index $(\operatorname{ord}_v f)$, converted to a natural number, is nonzero.
--
--   This is the non-vanishing of the leading Taylor coefficient of a function regular at a rational place: together with the companion equivalence describing when all coefficients of index $<e$ vanish, it identifies $\operatorname{ord}_v f$ as exactly the index of the first nonzero coefficient of the expansion of $f$ along a uniformiser $t$. It is used in the estimate [`ModularCurve.JZero.jensen_bad_at_le`](thm.html#ModularCurve.JZero.jensen_bad_at_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorCoeff_ord_ne_zero.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorCoeff_ord_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    taylorCoeff v t (v.ord f).toNat f ≠ 0 := by sorry
