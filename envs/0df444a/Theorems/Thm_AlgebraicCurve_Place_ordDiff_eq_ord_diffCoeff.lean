-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff
-- name    : AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/9b156dc4-1387-545b-8328-21470075c19f
-- title:
--   Order of a differential is independent of the uniformiser
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ of characteristic zero, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing $\operatorname{image}(K \to F)$, distinct from $F$ itself, whose ring is a principal ideal ring; write $\operatorname{ord}_v(f)$ for $-\log$ of the associated adic valuation of $f$, so that $\operatorname{ord}_v$ is the normalised integer-valued order function at $v$. Let $t \in F$ satisfy $\operatorname{ord}_v(t) = 1$, and let $\omega \in \Omega_{F/K}$ be a Kähler differential. Then $\operatorname{ordDiff}_v(\omega) = \operatorname{ord}_v\bigl(\operatorname{diffCoeff}(t, \omega)\bigr)$, where $\operatorname{diffCoeff}(s, \omega)$ denotes a chosen $g \in F$ with $\omega = g \cdot \mathrm{d}s$ when such a $g$ exists and $0$ otherwise, and where $\operatorname{ordDiff}_v(\omega)$ is by definition $\operatorname{ord}_v\bigl(\operatorname{diffCoeff}(t_v, \omega)\bigr)$ for one fixed choice $t_v$ of an element of $F$ of order $1$ at $v$. Thus the value computed from the fixed choice agrees with the value computed from an arbitrary $t$ of order $1$, with no hypothesis on $\omega$.
--
--   This is the well-definedness statement for the order of a differential at a place of a function field of one variable in characteristic zero: the integer $\operatorname{ord}_v(\omega)$ depends only on $\omega$ and $v$, not on the uniformiser used to express $\omega$ as $g\,\mathrm{d}t$. It underlies the comparison of `ordDiff` with the order of the associated differential and is used in the estimates for Wronskian differentials and heights on the modular curve $X_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ord (AlgebraicCurve.Place.diffCoeff t ω) := by sorry
