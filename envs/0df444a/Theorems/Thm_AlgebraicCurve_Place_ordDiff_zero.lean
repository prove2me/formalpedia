-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ordDiff_zero
-- name    : AlgebraicCurve.Place.ordDiff_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6f269f67-f826-5b30-9fae-a2c8d24bb9ba
-- title:
--   The zero differential has order 0 at every place
-- statement:
--   Let $K$ be a field of characteristic zero and $F$ a field extension of $K$ such that, for a given element $x \in F$, the extension $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and whose ring is a principal ideal ring. Recall the relevant definitions: `v.uniformizer_alt` is a chosen element $t \in F$ with `v.ord t = 1` if one exists and $0$ otherwise; for $t \in F$ and a Kähler differential $\omega \in \Omega_{F/K}$, `Place.diffCoeff t ω` is a chosen $g \in F$ with $\omega = g \cdot D_{K,F}(t)$ if one exists and $0$ otherwise; and `v.ordDiff ω` is `v.ord` of `Place.diffCoeff v.uniformizer_alt ω`. The assertion is that `v.ordDiff 0 = 0`, that is, the order at $v$ of the zero differential is $0$, in accordance with the convention $\operatorname{ord}_v(0) = 0$ for functions.
--
--   This is the normalisation fact underlying the definition of the order of a differential at a place; because of it, the additivity rule for $\operatorname{ord}_v(g\,\omega)$ must carry explicit nonvanishing hypotheses. It is used in the description of the regular differentials of a curve ([`AlgebraicCurve.mem_regularDiffs_iff`](thm.html#AlgebraicCurve.mem_regularDiffs_iff)) and in the treatment of coefficient maps on modular curves ([`ModularCurve.coeffMap_coeffEmb_of_ringHom`](thm.html#ModularCurve.coeffMap_coeffEmb_of_ringHom), [`ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom`](thm.html#ModularCurve.coeffMap_mem_laurentBaseChange_of_ringHom)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ordDiff_zero.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ordDiff_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by sorry
