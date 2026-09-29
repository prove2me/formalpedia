-- Prove2me | Theorems.Thm_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_isPurelyInseparable
-- name    : AlgebraicCurve.WeilDatum.pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_isPurelyInseparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e31317f8-6ca3-5967-bb52-d668ff96df3c
-- title:
--   Pairing invariance under purely inseparable pullback and pushforward
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, both satisfying `HasPrincipalDivisors` over $K$ (every nonzero element has a divisor recording its orders at all places and of degree $0$). Let $u : F \to F'$ be a $K$-algebra map whose underlying ring map is integral, such that $F'$ is a finite module over $F$ for the algebra structure induced by $u$, is purely inseparable over $F$, and satisfies the fundamental identity along $u$: for each place $v$ of $F$, $\sum_{w \mid v} e(w)\,\deg(w) = [F' : F]\,\deg(v)$. Assume further that every place of $F$ and every place of $F'$ is rational, i.e. $K$ surjects onto the residue field. Fix $n \in \mathbb{N}$, a Weil datum $d = (D_1, D_2, f_1, f_2)$ of order $n$ on $F'$ and a Weil datum $d_0$ of order $n$ on $F$ (so $f_i \neq 0$, $\operatorname{ord}_v f_1 = n D_1(v)$, $\operatorname{ord}_v f_2 = n D_2(v)$, the supports of $D_1$ and $D_2$ are disjoint, and the places in either support are rational). Suppose $D_1 = u^{*}(d_0.D_1)$, $f_1 = u(d_0.f_1)$, $d_0.D_2 = u_{*}(D_2)$, and $d_0.f_2 = N_{F'/F}(f_2)$. Then the two pairings agree in $K$: $\operatorname{evalFun}(f_1, D_2)/\operatorname{evalFun}(f_2, D_1) = \operatorname{evalFun}(d_0.f_1, d_0.D_2)/\operatorname{evalFun}(d_0.f_2, d_0.D_1)$.
--
--   This is the adjunction (projection) formula for the divisorial Weil pairing along a finite purely inseparable map of function fields: the pairing of a pulled-back first divisor against a second divisor on $F'$ equals the pairing of the first divisor against the pushed-forward second divisor on $F$. It is used in the comparison of Weil pairings under the $q$-expansion Frobenius, via [`AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom_of_isPurelyInseparable`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom_of_isPurelyInseparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_isPurelyInseparable.lean

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

theorem AlgebraicCurve.WeilDatum.pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_isPurelyInseparable
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u)
    (hpi : letI := algebraAlong u; IsPurelyInseparable F F') (hFI : FundamentalIdentityAlong K u hu)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {n : ℕ} (d : WeilDatum K F' n) (d₀ : WeilDatum K F n)
    (hD₁ : d.D₁ = Divisor.pullbackAlong u hu d₀.D₁) (hf₁ : d.f₁ = u d₀.f₁)
    (hD₂ : d₀.D₂ = Divisor.pushforwardAlong u hu d.D₂)
    (hf₂ : d₀.f₂ = (letI := algebraAlong u; Algebra.norm F d.f₂)) :
    d.pairing = d₀.pairing := by sorry
