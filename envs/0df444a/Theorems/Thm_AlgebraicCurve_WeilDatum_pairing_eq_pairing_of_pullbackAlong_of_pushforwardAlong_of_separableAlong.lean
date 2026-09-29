-- Prove2me | Theorems.Thm_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
-- name    : AlgebraicCurve.WeilDatum.pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/ea800dd3-fa63-567e-b37f-07bd41942650
-- title:
--   Weil pairing adjunction along a finite separable map
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ such that every nonzero element of $F$, resp. of $F'$, has a divisor of degree zero (`HasPrincipalDivisors`: for each $f \ne 0$ there is a finitely supported integer combination of places whose value at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$; here a place is a valuation subring of the field, containing the image of $K$, not equal to the whole field and a principal ideal ring). Let $u : F \to F'$ be a $K$-algebra map whose underlying ring homomorphism is integral, and assume that $F'$ is a finite $F$-module and separable over $F$ for the $F$-algebra structure given by $u$, and that every place of $F$ and every place of $F'$ is rational, i.e. the map from $K$ to its residue field is surjective. Fix $n \in \mathbb{N}$ and Weil data $d$ on $F'$ and $d_0$ on $F$ of order $n$, each consisting of divisors $D_1, D_2$ and nonzero functions $f_1, f_2$ with $\mathrm{ord}_v f_i = n\,D_i(v)$ at every place, with $D_1$ and $D_2$ having disjoint supports and every place in the support of $D_1$ or $D_2$ rational. Assume $d.D_1$ is the pullback of $d_0.D_1$ along $u$, $d.f_1 = u(d_0.f_1)$, $d_0.D_2$ is the pushforward of $d.D_2$ along $u$, and $d_0.f_2$ is the norm $N_{F'/F}(d.f_2)$ taken for the $F$-algebra structure given by $u$. Then the two pairings agree in $K$: $d.\mathrm{pairing} = d_0.\mathrm{pairing}$, where the pairing of a datum is $\mathrm{evalFun}(f_1, D_2)/\mathrm{evalFun}(f_2, D_1)$.
--
--   This is the adjunction (or projection) formula for Weil's pairing of functions against divisors on curves: pulling back the first argument along a finite separable map and pushing forward the second leaves the pairing unchanged. It is used by [`AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom), which transports the statement to the level of pairings of divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

set_option autoImplicit false

theorem AlgebraicCurve.WeilDatum.pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u) (hsep : SeparableAlong K u)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {n : ℕ} (d : WeilDatum K F' n) (d₀ : WeilDatum K F n)
    (hD₁ : d.D₁ = Divisor.pullbackAlong u hu d₀.D₁) (hf₁ : d.f₁ = u d₀.f₁)
    (hD₂ : d₀.D₂ = Divisor.pushforwardAlong u hu d.D₂)
    (hf₂ : d₀.f₂ = (letI := algebraAlong u; Algebra.norm F d.f₂)) :
    d.pairing = d₀.pairing := by sorry
