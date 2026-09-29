-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg
-- name    : AlgebraicCurve.Place.ord_diffCoeff_D_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/15c05da3-b3ab-5a8f-94a8-a95db8b657ce
-- title:
--   Regularity of df/dt at a place with uniformiser t
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ of characteristic zero, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$ in the sense of this development: a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and whose underlying ring is a principal ideal ring; for $h \in F$ the integer $\operatorname{ord}_v(h)$ is $-\log$ of the value of $h$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of that subring. Assume $t \in F$ satisfies $\operatorname{ord}_v(t) = 1$, and $f \in F$ satisfies $0 \le \operatorname{ord}_v(f)$. Write $\mathrm{D}_{K,F} f$ for the universal derivation of $f$ in $\Omega_{F/K}$, and let `diffCoeff t` send a Kähler differential $\omega$ to some chosen $g \in F$ with $\omega = g \cdot \mathrm{D}_{K,F} t$ if such a $g$ exists, and to $0$ otherwise. The conclusion is that $0 \le \operatorname{ord}_v\bigl(\mathrm{diffCoeff}\, t\,(\mathrm{D}_{K,F} f)\bigr)$.
--
--   This is the local statement that, for a uniformiser $t$ at $v$, the derivation $d/dt$ carries the valuation ring of $v$ into itself: the coefficient of $df$ against $dt$ is regular at $v$ whenever $f$ is. It underlies the companion results computing the order of a differential, among them [`AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one`](thm.html#AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one), [`AlgebraicCurve.Place.ordDiff_D_nonneg`](thm.html#AlgebraicCurve.Place.ordDiff_D_nonneg) and [`AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff`](thm.html#AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff), and hence the independence of that order from the chosen uniformiser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_diffCoeff_D_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1) {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) := by sorry
