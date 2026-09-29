-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforward_div_of_isSeparable
-- name    : AlgebraicCurve.Divisor.pushforward_div_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/16100a1f-79e9-57d7-97ee-5dd96f8d5744
-- title:
--   Push-forward of div f is div N_{F'/F}(f), separable case
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, forming a scalar tower $K \subseteq F \subseteq F'$, with $F'/F$ finite-dimensional and separable, and assume `HasPrincipalDivisors K F'`, i.e. every nonzero $g \in F'$ admits a divisor $D$ (a finitely supported integer-valued function on the places of $F'$ over $K$, a place being a valuation subring of $F'$ containing the image of $K$, different from all of $F'$, and a principal ideal ring) with $D(w) = \operatorname{ord}_w(g) = -\log$ of the associated height-one-spectrum valuation of $g$ at every place $w$, and of degree $0$. Let $f \in F'$ be nonzero, let $D$ be a divisor of $F'/K$ with $D(w) = \operatorname{ord}_w(f)$ for every place $w$ of $F'$ over $K$, and let $E$ be a divisor of $F/K$ with $E(v) = \operatorname{ord}_v(\mathrm{N}_{F'/F}(f))$ for every place $v$ of $F$ over $K$. Then the push-forward of $D$ to $F$, which sends each place $w$ to its restriction $w \cap F$ weighted by the residue degree $[\kappa(w) : \kappa(w \cap F)]$, equals $E$.
--
--   This is the compatibility of the norm with divisors: the push-forward along $F' / F$ of the principal divisor of $f$ is the principal divisor of $\mathrm{N}_{F'/F}(f)$, here in the form of an equality of divisors under separability of $F'/F$ rather than a characteristic-zero assumption. It underlies Weil reciprocity for norms along separable extensions and, through it, the divisorial construction of the Weil pairing, as used by [`AlgebraicCurve.weilReciprocity_algebraMap_of_isSeparable`](thm.html#AlgebraicCurve.weilReciprocity_algebraMap_of_isSeparable) and [`AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible_coprime_of_isAlgClosed`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible_coprime_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforward_div_of_isSeparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforward_div_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) {D : Divisor K F'} (hD : ∀ w, D w = w.ord f) {E : Divisor K F} (hE : ∀ v, E v = v.ord (Algebra.norm F f)) : Divisor.pushforward F D = E := by sorry
