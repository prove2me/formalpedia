-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
-- name    : AlgebraicCurve.Place.ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/44160fe8-f85d-5afb-b707-a7ff3c522c30
-- title:
--   Ramification in tame Kummer extensions of a function field
-- statement:
--   Let $K$ be an algebraically closed field and let $F$, $F'$ be fields with $K$-algebra structures and an $F$-algebra structure on $F'$ compatible with the maps from $K$, and assume $F'$ is a curve over $K$ in the sense of `IsCurveOver`: every nonzero element of $F'$ has an associated degree-zero divisor whose value at each place is the order of that element there, each place of $F'/K$ has residue field finite over $K$, and $\Omega[F'⁄K]$ is free of rank one over $F'$. Let $n$ be a natural number whose image in $K$ is nonzero, and let $b \in F$ be nonzero. Assume $F'$ is finite-dimensional over $F$ and is a splitting field of $X^n - C\,b$ over $F$, with $\operatorname{finrank}_F F' = n$. Then for every place $w$ of $F'$ over $K$ — that is, a proper valuation subring of $F'$ containing the image of $K$ and which is a principal ideal ring — the ramification index of $w$ over $F$, defined as the least positive natural number of the form $\operatorname{ord}_w(\text{image of } f)$ for some nonzero $f \in F$, equals the natural-number quotient $n / \gcd\bigl(n, |\operatorname{ord}_{w|_F} b|\bigr)$, where $w|_F$ is the place of $F$ obtained by pulling back the valuation subring of $w$ along $F \to F'$ and $\operatorname{ord}$ denotes the integer-valued order function of a place.
--
--   This is the standard ramification formula for tame Kummer extensions $F' = F(b^{1/n})$ of a function field in one variable over an algebraically closed constant field, in the form $e(w\mid v) = n/\gcd(n, \operatorname{ord}_v b)$. It is used to compute ramification indices for the covering of modular curves attached to a level structure, via [`ModularCurve.FullLevel.ramificationIndex_xHFunctionFieldC_levelH_modularFunctionFieldC_eq_of_liesOverPrime`](thm.html#ModularCurve.FullLevel.ramificationIndex_xHFunctionFieldC_levelH_modularFunctionFieldC_eq_of_liesOverPrime), and its proof invokes the degree formula $\sum_w e_w f_w = [F':F]$ together with the characterisation of places of residue degree one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
    {K : Type*} [Field K] [IsAlgClosed K]
    {F : Type*} [Field F] [Algebra K F]
    {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [IsCurveOver K F']
    (n : ℕ) (hn : (n : K) ≠ 0) (b : F) (hb : b ≠ 0)
    [FiniteDimensional F F'] [IsSplittingField F F' (X ^ n - C b)]
    (hdeg : Module.finrank F F' = n)
    (w : Place K F') :
    w.ramificationIndex F = n / Nat.gcd n ((w.restrict F).ord b).natAbs := by sorry
