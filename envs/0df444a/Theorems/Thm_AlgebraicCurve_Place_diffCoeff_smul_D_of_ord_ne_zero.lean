-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero
-- name    : AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/fdd7becf-e61a-5010-81c7-31870dd97e68
-- title:
--   The chosen coefficient reproduces ω: diffCoeff(t,ω) dt=ω
-- statement:
--   Let $K$ be a field of characteristic zero and $F$ a field extension of $K$. Let $x \in F$ be an element such that $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F/K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring of $F$ containing the image of $K$ under the structure map, different from all of $F$, and whose ideals are all principal; let $v.\mathrm{ord}$ denote the associated integer valuation, the negative of the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $v$. Let $t \in F$ satisfy $v.\mathrm{ord}\,t \neq 0$, and let $\omega$ be a Kähler differential in $\Omega_{F/K}$. Then $\mathrm{diffCoeff}(t, \omega) \cdot dt = \omega$, where $dt$ is `KaehlerDifferential.D K F t` and $\mathrm{diffCoeff}(t,\omega)$ is defined as a choice of $g \in F$ with $\omega = g \cdot dt$ when such a $g$ exists, and $0$ otherwise. In other words, under these hypotheses the defining case of `diffCoeff` is the one that applies, and the chosen scalar is genuinely a coefficient of $\omega$ against $dt$.
--
--   This is the formal counterpart of the statement that, for a function field of transcendence degree one in characteristic zero, every element of nonzero order at a place is separating, so that $\Omega_{F/K}$ is a one-dimensional $F$-space with basis $dt$. It is the fact underlying the well-definedness of the order of a differential at a place, and is used by the results computing $v.\mathrm{ordDiff}$ of $dt$ and its lower bounds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω := by sorry
