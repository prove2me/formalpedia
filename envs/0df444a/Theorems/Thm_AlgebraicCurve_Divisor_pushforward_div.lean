-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforward_div
-- name    : AlgebraicCurve.Divisor.pushforward_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/43ae4dea-33d1-5910-bdc6-0deb25fc7373
-- title:
--   Pushforward of a principal divisor is the divisor of the norm
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ both $K$-algebras and $F'$ an $F$-algebra, the three algebra structures forming a scalar tower, with $F'/F$ finite and separable and $F$ of characteristic zero; assume moreover that $F'/K$ has principal divisors, i.e. that for every nonzero $g \in F'$ there is a finitely supported function $D$ on the places of $F'/K$ with $D(w) = \operatorname{ord}_w g$ for all $w$ and $\deg D = 0$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring, and $\operatorname{ord}_v(g)$ is $-\log$ of the associated height-one adic valuation of $g$; a divisor is a finitely supported integer-valued function on places. Let $f \in F'$ be nonzero, let $D$ be a divisor of $F'/K$ with $D(w) = \operatorname{ord}_w f$ for every place $w$ of $F'/K$, and let $E$ be a divisor of $F/K$ with $E(v) = \operatorname{ord}_v(N_{F'/F}(f))$ for every place $v$ of $F/K$. The conclusion is that the pushforward of $D$ along $F' / F$ equals $E$, where the pushforward is the additive map sending the generator at $w$ to $[\,\kappa(w) : \kappa(w|_F)\,]$ times the generator at the restriction of $w$ to $F$, the multiplicity being the residue degree $\operatorname{finrank}_{\kappa(w|_F)} \kappa(w)$.
--
--   This is the divisor-level form of the classical norm formula $\pi_*(\operatorname{div} f) = \operatorname{div}(N_{F'/F} f)$ for a finite separable extension of function fields, stated without choosing representatives for the divisors. It is used in the norm step of Weil reciprocity along a subfield ([`AlgebraicCurve.weilReciprocity_algebraMap`](thm.html#AlgebraicCurve.weilReciprocity_algebraMap)) and in the injectivity argument for divisorial Weil pairing data ([`AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforward_div.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforward_div {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) {D : Divisor K F'} (hD : ∀ w, D w = w.ord f) {E : Divisor K F} (hE : ∀ v, E v = v.ord (Algebra.norm F f)) : Divisor.pushforward F D = E := by sorry
