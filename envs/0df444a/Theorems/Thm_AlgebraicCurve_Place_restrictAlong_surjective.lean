-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
-- name    : AlgebraicCurve.Place.restrictAlong_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f685dcec-8c0f-5ba0-96a3-c999ac4864ce
-- title:
--   Surjectivity of restriction of places along a finite separable map
-- statement:
--   Let $K$ be a field and let $F$, $F'$ be field extensions of $K$. Let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and transport along $\varphi$ the $F$-algebra structure on $F'$; assume `FiniteAlong`, i.e. that $F'$ is a finite $F$-module for this structure, and `SeparableAlong`, i.e. that $F'$ is a separable $F$-algebra for it. Here a place of a $K$-extension $L$ (the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22)) consists of a valuation subring of $L$ that contains the image of $K$ under the structure map, is not all of $L$, and is a principal ideal ring; and `Place.restrictAlong` sends a place $w$ of $F'/K$ to the place of $F/K$ whose valuation subring is the preimage of that of $w$ under $\varphi$ (its non-triviality and principality being inherited). The assertion is that the resulting map from places of $F'/K$ to places of $F/K$, $w \mapsto w.\mathrm{restrictAlong}\ \varphi$, is surjective: every place of $F/K$ is the restriction along $\varphi$ of some place of $F'/K$.
--
--   This is the existence half of lying-over for places of a function field: each discrete valuation ring of $F$ containing $K$ admits a prolongation to $F'$ when $F'/F$ is finite separable. It underlies the fibre-counting statements for the restriction map (degree and ramification identities along a correspondence) and, through them, surjectivity statements for push-forward maps on divisor classes and on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_restrictAlong_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_surjective
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong K φ) (hsep : AlgebraicCurve.SeparableAlong K φ) :
    Function.Surjective (fun w : AlgebraicCurve.Place K F' => w.restrictAlong φ hφ) := by sorry
