-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_single_one
-- name    : AlgebraicCurve.Divisor.pushforwardAlong_single_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/0d82f430-0f99-5719-9371-d44e5448507c
-- title:
--   Push-forward of a degree-one place over a degree-one place
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras, let $\psi \colon F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and let $W$ be a place of $F'$ over $K$, that is, a valuation subring of $F'$ which contains the image of $K$, is not all of $F'$, and is a principal ideal ring. Write $W|_\psi$ for the place `W.restrictAlong ψ hψ` of $F$ over $K$, obtained by pulling back the valuation subring $W$ along $\psi$ viewed as the structure map making $F'$ an $F$-algebra. Assume that the degree of $W$, namely the $K$-dimension of the residue field of $W$, equals $1$, and likewise that the degree of $W|_\psi$ equals $1$. The conclusion is that the push-forward homomorphism on divisors along $\psi$ — the additive map $\mathrm{Div}(F'/K) = (\text{Place } K\,F' \to_{0} \mathbb{Z}) \to \mathrm{Div}(F/K)$ sending $w \mapsto n$ to $w|_\psi \mapsto n \cdot f(w)$, where $f(w)$ is the inertia degree of $w$ over $F$ — takes the prime divisor $W$ with multiplicity $1$ to the prime divisor $W|_\psi$ with multiplicity $1$.
--
--   This is the standard computation of the push-forward (conorm–norm) of a prime divisor under a finite extension of function fields, in the special case where both the place upstairs and the place below it are rational: the residue degree is then forced to be $1$, so no multiplicity appears. It is used to express the push-forward legs of Hecke and degeneracy correspondences on divisors of modular curves as plain sums of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardAlong_single_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.pushforwardAlong_single_one
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : AlgebraicCurve.Place K F')
    (hW : W.deg = 1) (hV : (W.restrictAlong ψ hψ).deg = 1) :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by sorry
