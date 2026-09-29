-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
-- name    : AlgebraicCurve.Place.taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/2088a701-e2c1-5f31-a189-95f946b33a47
-- title:
--   Shift of Taylor coefficients along a uniformiser
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$ under the structure map, different from $F$ itself, and whose underlying ring is a principal ideal ring. Let $t,f\in F$ and $r\in\mathbb{N}$ be arbitrary. Recall that the evaluation $v.\mathrm{evalAt}(g)\in K$ is the residue of $g$ in the residue field of the valuation ring, transported back to $K$, when $g$ lies in the valuation subring, and $0$ otherwise; that the Taylor remainders are defined by $\rho_0(g)=g$ and $\rho_{s+1}(g)=\bigl(\rho_s(g)-\mathrm{evalAt}(\rho_s(g))\bigr)t^{-1}$, the constant being viewed in $F$; and that the $r$-th Taylor coefficient of $g$ is $\mathrm{evalAt}(\rho_r(g))$. The assertion is the index shift
--   $$\mathrm{taylorCoeff}\,v\,t\,(r+1)\,f=\mathrm{taylorCoeff}\,v\,t\,r\,\bigl(\rho_1(f)\bigr),\qquad \rho_1(f)=\bigl(f-\mathrm{evalAt}(f)\bigr)t^{-1}.$$
--   No hypothesis is imposed on $v$, on $t$ (it need not be a uniformiser at $v$) or on $f$ (it need not lie in the valuation subring).
--
--   This is the coefficient form of the recursion defining the Taylor expansion of an element of $F$ at a place along an element $t$: passing to the first remainder lowers the order of a coefficient by one. It is the inductive step used by the statements on Taylor coefficients of elements of $K$, on products, and on the associated polynomial truncations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorCoeff_succ_eq_taylorCoeff_taylorRem_one.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorCoeff_succ_eq_taylorCoeff_taylorRem_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorCoeff v t (r + 1) f = taylorCoeff v t r (taylorRem v t f 1) := by sorry
