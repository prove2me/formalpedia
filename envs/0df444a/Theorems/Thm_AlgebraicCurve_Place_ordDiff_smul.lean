-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul
-- name    : AlgebraicCurve.Place.ordDiff_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/bf02357a-bbbb-57d3-a3e9-16e475b6318c
-- title:
--   Order of a differential scales: ordᵥ(gω)=ordᵥ g+ordᵥω
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra and $\operatorname{char} K = 0$, and let $x \in F$ be an element such that $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F/K$ in the sense of this development: a valuation subring of $F$ containing $\operatorname{algebraMap} K F(a)$ for every $a \in K$, distinct from $F$ itself, and whose ring is a principal ideal ring. For $f \in F$, $\operatorname{ord}_v f$ denotes $-\log$ of the value of $f$ under the adic valuation of the associated height-one prime, an element of $\mathbb{Z}$; `uniformizer_alt` is a chosen $t \in F$ with $\operatorname{ord}_v t = 1$ when such a $t$ exists and $0$ otherwise; for $t \in F$ and $\omega \in \Omega_{F/K}$, $\operatorname{diffCoeff} t\,\omega$ is a chosen $g \in F$ with $\omega = g \cdot D_{K/F}t$ when one exists and $0$ otherwise; and $\operatorname{ordDiff}_v \omega := \operatorname{ord}_v(\operatorname{diffCoeff} (\mathrm{uniformizer\_alt})\,\omega)$. The assertion is that for every nonzero $g \in F$ and every nonzero Kähler differential $\omega \in \Omega_{F/K}$ one has $\operatorname{ordDiff}_v(g \cdot \omega) = \operatorname{ord}_v g + \operatorname{ordDiff}_v \omega$. Both nonvanishing hypotheses are needed, since the conventions above assign order $0$ to the zero element and to the zero differential.
--
--   This is the standard multiplicativity of the order of a differential at a place of a function field of one variable, in the form used to show that the divisor of a nonzero differential is well defined up to the divisor of a function. It is used in the characterisation of regular differentials on an algebraic curve and in the comparison of coefficient maps for differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ordDiff_smul.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ordDiff_smul {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by sorry
