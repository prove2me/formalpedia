-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction
-- name    : AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/84ef0dcc-1d35-5f2e-8273-53f9113f7ef2
-- title:
--   Deuring reduction of a principal divisor along A
-- statement:
--   Let $K$, $F$, $E$, $FE$ be fields with algebra maps making $K\to E\to FE$ and $K\to F\to FE$ compatible towers, with $K$ algebraically closed of characteristic $0$ and $E$ algebraically closed. Assume $F$ contains an element transcendental over $K$ over whose generated subfield $F$ is finite-dimensional, and likewise for $FE$ over $E$; assume moreover `IsCurveOver K F` and `IsCurveOver E FE`, i.e. for each of the two extensions every nonzero function admits a finitely supported divisor recording its orders at all places and having degree $0$, every place has residue field finite-dimensional over the constant field, and the module of Kähler differentials is free of rank one. Assume $FE$ is generated over $E$ by the image of $F$. Let $A$ be a valuation subring of $E$ containing the image of $K$ such that every $a\in A$ satisfies $v_A(a-k)<1$ for some $k\in K$, and let $r\colon$ (places of $FE/E$) $\to$ (places of $F/K$) satisfy: $f\in F$ lies in the valuation subring of $r(P)$ exactly when $v_P(f-a)<1$ for some $a\in A$. Here a place is a proper valuation subring containing the constant field which is a principal ideal ring, and $\operatorname{ord}$ is minus the logarithm of its associated adic valuation. Let $O$ be a valuation subring of $FE$ with $O\cap E=A$ (in the sense that $c\in E$ lies in $O$ iff $c\in A$) and $\rho\colon O\to F$ a ring homomorphism with kernel the maximal ideal of $O$ which fixes every element of $F$ (each $f\in F$ lies in $O$ and $\rho(f)=f$). Then for $g\in O$ with $\rho(g)\neq 0$, for any finitely supported $D_g$ on the places of $FE/E$ with $D_g(P)=\operatorname{ord}_P(g)$ for all $P$, and for every place $v$ of $F/K$, the pushforward of $D_g$ along $r$ takes at $v$ the value $\operatorname{ord}_v(\rho(g))$, i.e. $\sum_{r(P)=v}\operatorname{ord}_P(g)=\operatorname{ord}_v(\rho(g))$.
--
--   This is Deuring's theorem on constant reduction: for a constant field extension $FE=F\cdot E$ and a valuation subring $A$ of $E$ with residue field $K$, the reduction map on places carries the principal divisor of $g$ to the principal divisor of the reduced function $\rho(g)$. It underlies the comparison of Riemann–Roch spaces across the constant field extension and the vanishing statement for $\mathrm{Pic}^0$ under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_eq_ord_of_retraction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) (Dg : Divisor E FE) (hDg : ∀ P : Place E FE, Dg P = P.ord (g : FE))
    (v : Place K F) :
    Finsupp.mapDomain r Dg v = v.ord (ρ g) := by sorry
