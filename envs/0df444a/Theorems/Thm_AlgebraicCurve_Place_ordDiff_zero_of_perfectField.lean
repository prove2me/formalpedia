-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ordDiff_zero_of_perfectField
-- name    : AlgebraicCurve.Place.ordDiff_zero_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/d1ffc033-4926-5e87-a50f-534af731f3ef
-- title:
--   Order of the zero differential at a place vanishes
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and suppose $K$ is perfect. Let $x \in F$ be an element such that $F$ is algebraic over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`, and let $v$ be a place of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. The conclusion is that $v.\mathrm{ordDiff}\,0 = 0$. Here, for a differential $\omega \in \Omega_{F/K}$, $v.\mathrm{ordDiff}\,\omega$ is defined as the value of $v.\mathrm{ord}$ at $\mathrm{diffCoeff}\,t\,\omega$, where $t = v.\mathrm{uniformizer\_alt}$ is a chosen element of $F$ with $v.\mathrm{ord}\,t = 1$ when such an element exists (and $0$ otherwise), and $\mathrm{diffCoeff}\,t\,\omega$ is a chosen $g \in F$ with $\omega = g \cdot D_{K/F}(t)$ when such a $g$ exists (and $0$ otherwise). Thus the assertion is that the coefficient assigned to the zero differential against $D(t)$ has $v.\mathrm{ord}$ equal to $0$.
--
--   This records the conventional value of the order function on differentials at the zero differential, in the setting of a perfect constant field, where a uniformizer at $v$ is available and is a separating element. It is used in the comparison of `ordDiff` with the order of a differential over a perfect base field and in the estimate of `ordDiff` for differentials of the form $g \cdot D$ arising from Weierstrass data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ordDiff_zero_of_perfectField.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ordDiff_zero_of_perfectField {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by sorry
