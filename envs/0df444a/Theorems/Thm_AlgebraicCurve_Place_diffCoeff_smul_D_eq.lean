-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq
-- name    : AlgebraicCurve.Place.diffCoeff_smul_D_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c96609bb-aa30-5ef8-9162-8ae441a6ce18
-- title:
--   Uniqueness of the coefficient against dt
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $K$ have characteristic zero. Let $x \in F$ be an element such that $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}` (no transcendence of $x$ itself is assumed). Let $v$ be a place of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F$ containing the image of $K$ under the structure map, different from $F$ itself, and whose underlying ring is a principal ideal ring. Write $\operatorname{ord}_v f = -\log\, v_{\mathrm{adic}}(f)$ for the associated integer-valued order function, built from the valuation attached to the height-one prime of the valuation subring. Let $t \in F$ satisfy $\operatorname{ord}_v t \neq 0$, and let $g \in F$ be arbitrary. Then $\mathrm{diffCoeff}\,t\,(g \cdot D_{K/F} t) = g$, where $\mathrm{diffCoeff}\,t\,\omega$ is defined to be a chosen $h \in F$ with $\omega = h \cdot D_{K/F} t$ when such an $h$ exists and $0$ otherwise, and $D_{K/F}$ is the universal $K$-derivation of $F$ into the module of Kähler differentials $\Omega[F/K]$.
--
--   This is the uniqueness half of the statement that $\Omega[F/K]$ is a one-dimensional $F$-vector space with basis $dt$ for any $t$ of nonzero order at a place, in characteristic zero; it makes the coefficient extraction $\mathrm{diffCoeff}$ well behaved, and hence the order of a differential at a place well defined. It is used in the computation of the order of a differential at $v$, for instance in [`AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one`](thm.html#AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one) and [`AlgebraicCurve.Place.ordDiff_D_nonneg`](thm.html#AlgebraicCurve.Place.ordDiff_D_nonneg), and in the comparison of regular differentials under extension of the constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.diffCoeff_smul_D_eq {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g := by sorry
