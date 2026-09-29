-- Prove2me | Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence
-- name    : AlgebraicCurve.DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/1912701b-6e1e-5ab5-8ccb-6dae6a5ed098
-- title:
--   Correspondence adjointness of the divisorial Weil pairing
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a $K$-algebra field satisfying `IsCurveOver K F`: every nonzero $f\in F$ has a degree-zero divisor whose coefficient at each place $v$ is $\operatorname{ord}_v f$, each place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Let $F'$ be a further $K$-algebra field in which every nonzero element likewise has a principal divisor of degree $0$, and let $\varphi,\psi\colon F\to F'$ be $K$-algebra maps whose underlying ring maps are integral. Assume the fundamental identity holds for $F'$ viewed as an $F$-algebra through $\varphi$ (hypothesis `hFIφ`) and through $\psi$ (`hFIψ`), and that $F'$ is a finite $F$-module through $\psi$ (`hfinψ`) and through $\varphi$ (`hfinφ`), with the pushforward norm formula for divisors in each case (`hNψ`, `hNφ`). Let $n$ be a nonzero natural number and $e$ a `DivisorialWeilPairingData K F n`, that is, a pairing `e.pair` on the $n$-torsion of $\mathrm{Pic}^0(F/K)$ with values in $K$ which agrees with the pairing attached to every Weil datum of level $n$ and which allows any torsion class to be represented by a degree-zero divisor supported on rational places avoiding a prescribed finite set of places. Let $x,y\in\mathrm{Pic}^0(F/K)$ satisfy $n\cdot x=0$ and $n\cdot y=0$, and assume in addition that $n$ annihilates $\psi_*\varphi^*x$ and $\varphi_*\psi^*y$, where $\psi_*\varphi^*$ denotes the map `Pic0.correspondence φ ψ …` induced by pulling back divisors along $\varphi$ and pushing forward along $\psi$, and $\varphi_*\psi^*$ is `Pic0.correspondence ψ φ …`. Then $e(\psi_*\varphi^*x,\,y)=e(x,\,\varphi_*\psi^*y)$, the two arguments being taken as $n$-torsion classes via the stated annihilation hypotheses.
--
--   This is the adjointness property of a divisorial correspondence and its transpose with respect to the Weil pairing on the Jacobian of a curve. It is one clause of the level-$n$ Weil pairing package on $\mathrm{Pic}^0$, used in the construction [`AlgebraicCurve.Pic0.exists_weilPairing`](thm.html#AlgebraicCurve.Pic0.exists_weilPairing) and in the compatibility of the pairing on the Tate module with correspondences, and from there in the Galois- and Hecke-equivariance statements for pairings on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

set_option autoImplicit false

theorem AlgebraicCurve.DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    {F' : Type*} [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n)
    (x y : Pic0 K F) (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0)
    (hcx : (n : ℤ) • Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x = 0)
    (hcy : (n : ℤ) • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y = 0) :
    e.pair ⟨Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x, Pic0.mem_torsion.mpr hcx⟩
        ⟨y, Pic0.mem_torsion.mpr hy⟩
      = e.pair ⟨x, Pic0.mem_torsion.mpr hx⟩
          ⟨Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y, Pic0.mem_torsion.mpr hcy⟩ := by sorry
