-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
-- name    : AlgebraicCurve.Place.ramificationIndexAlong_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/56af88ce-a183-583e-854f-ce3846f64481
-- title:
--   Multiplicativity of the ramification index in a tower
-- statement:
--   Let $K$ be a field and let $F$, $F'$, $F''$ be fields equipped with $K$-algebra structures, let $\varphi \colon F \to F'$ and $\chi \colon F' \to F''$ be $K$-algebra homomorphisms, and assume that the underlying ring homomorphisms of $\varphi$, of $\chi$ and of $\chi \circ \varphi$ are integral. Let $W$ be a place of $F''$ over $K$, that is, a valuation subring of $F''$ containing the image of $K$, distinct from $F''$ itself, and a principal ideal ring. For a $K$-algebra homomorphism $\psi$ into a field carrying a place $w$, the ramification index of $w$ along $\psi$ is the least $n > 0$ such that $w.\mathrm{ord}(\psi(f)) = n$ for some nonzero $f$ in the source, the algebra structure on the source being the one transported along $\psi$; and the restriction of $w$ along $\psi$ is the place whose valuation subring is the preimage under $\psi$ of that of $w$. The assertion is the identity of natural numbers $$e(\chi \circ \varphi, W) = e(\chi, W) \cdot e\bigl(\varphi, W|_{\chi}\bigr),$$ where $W|_{\chi}$ denotes `Place.restrictAlong` of $W$ along $\chi$.
--
--   This is the multiplicativity of ramification indices in a tower of (integral) extensions of function fields, in the form used for places and their restrictions along $K$-algebra maps. It underlies the functoriality of divisor pullback along a composite, [`AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong`](thm.html#AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong), and the fundamental-identity computations over bifibres of a pair of morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndexAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : Place.ramificationIndexAlong (χ.comp φ) W = Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) := by sorry
