-- Prove2me | Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_pullbackAlong_eq_pair_pushforwardAlongHom
-- name    : AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bef169fe-38b3-5e22-93f5-c19386561005
-- title:
--   Adjunction for divisorial Weil pairings along a finite map
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$, $F'$ be $K$-algebras which are fields and satisfy `IsCurveOver K F`, `IsCurveOver K F'`: every nonzero function has a divisor of valuations, of degree zero, each place has residue field finite over $K$, and the module of Kähler differentials is free of rank one. Let $u : F \to F'$ be a $K$-algebra map whose underlying ring map is integral, and assume: `FundamentalIdentityAlong`, the fundamental identity for $F'$ as an $F$-algebra via $u$; `FiniteAlong`, that $F'$ is a finite $F$-module via $u$; and `NormFormulaAlong`, the pushforward norm formula for that extension. Let $n$ be a nonzero natural number and let $e'$, $e$ be divisorial Weil pairing data of order $n$ on $F'$ and on $F$ — that is, $K$-valued pairings on the $n$-torsion of $\mathrm{Pic}^0$ agreeing with the pairing of every Weil datum, together with a moving property producing representatives supported at rational places away from a given finite set. Let $x \in \mathrm{Pic}^0(K,F)$ and $y \in \mathrm{Pic}^0(K,F')$ be killed by $n$, let $D_0$ be a degree-zero divisor on $F$ with class $x$, and let $x'$ be the class of the pullback of $D_0$ along $u$ (of degree zero by the fundamental identity). Assuming in addition that $n$ kills $x'$ and kills the pushforward of $y$ along $u$, the conclusion is $e'(x', y) = e(x, u_* y)$, where $u_*$ is `Pic0.pushforwardAlongHom`.
--
--   This is the adjunction (functoriality) property of the Weil pairing under a finite morphism of curves, $e_{J'}(u^*x, y) = e_J(x, u_*y)$, stated for the divisorial description of the pairing on degree-zero divisor classes. It is used in the analysis of $p$-adic lattices and torsion in the Jacobians of modular curves under degeneracy maps, where the orthogonality of a toric part against pullbacks of torsion is reduced to pairings on the smaller curve; the divisor-level input is the comparison of Weil data under pullback and pushforward together with the characterisation of rational places by degree one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_pullbackAlong_eq_pair_pushforwardAlongHom.lean

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

theorem AlgebraicCurve.DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    {F' : Type*} [Field F'] [Algebra K F'] [IsCurveOver K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K u hu) (hfin : FiniteAlong K u) (hN : NormFormulaAlong K u hfin)
    {n : ℕ} [NeZero n] (e' : DivisorialWeilPairingData K F' n) (e : DivisorialWeilPairingData K F n)
    (x : Pic0 K F) (hx : (n : ℤ) • x = 0)
    (y : Pic0 K F') (hy : (n : ℤ) • y = 0)

    (D₀ : Divisor.degZero (K := K) (F := F)) (hD₀ : Pic0.mk D₀ = x)
    (x' : Pic0 K F') (hx'def : x' = Pic0.mk ⟨Divisor.pullbackAlong u hu (D₀ : Divisor K F),
        Divisor.pullbackAlong_mem_degZero u hu hFI D₀.2⟩) (hx' : (n : ℤ) • x' = 0)

    (hy₀ : (n : ℤ) • Pic0.pushforwardAlongHom u hu hfin hN y = 0) :
    e'.pair ⟨x', Pic0.mem_torsion.mpr hx'⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩
      = e.pair ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨Pic0.pushforwardAlongHom u hu hfin hN y, Pic0.mem_torsion.mpr hy₀⟩ := by sorry
