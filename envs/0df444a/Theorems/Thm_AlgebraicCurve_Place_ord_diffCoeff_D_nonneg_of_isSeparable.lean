-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable
-- name    : AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6d8aaf73-f4da-5fc8-918a-ec4506db231b
-- title:
--   Differentiation with respect to a uniformiser preserves 𝒪ᵥ
-- statement:
--   Let $K$ be a perfect field and $F$ a field extension of $K$, and suppose there is an element $x \in F$ with $F$ finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$, different from all of $F$, and whose underlying ring is a principal ideal ring; write $\operatorname{ord}_v$ for the associated normalised valuation, the negative of the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $v$. Let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, and assume $F$ is separable over $K(t)$. Then for every $f \in F$ with $\operatorname{ord}_v f \ge 0$ one has $\operatorname{ord}_v\bigl(\operatorname{diffCoeff} t\, (\mathrm{d}_{K/F} f)\bigr) \ge 0$, where $\operatorname{diffCoeff} t\, \omega$ denotes a chosen $g \in F$ with $\omega = g \cdot \mathrm{d}t$ in $\Omega_{F/K}$ when such a $g$ exists, and $0$ otherwise.
--
--   This is the statement that the derivation $f \mapsto \mathrm{d}f/\mathrm{d}t$ with respect to a uniformiser $t$ at $v$ maps the valuation ring of $v$ into itself, in the form used for function fields of one variable over a perfect constant field. It underlies the computation of the order of vanishing of differentials at a place, and is cited in the results on $\operatorname{ord}$ of $\mathrm{d}f$ for $f$ with positive order and on orders of pullbacks of differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F}
    (ht : v.ord t = 1)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F] {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) := by sorry
