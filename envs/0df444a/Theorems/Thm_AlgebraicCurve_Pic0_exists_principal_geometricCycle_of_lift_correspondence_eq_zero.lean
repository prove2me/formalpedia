-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero
-- name    : AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/33bf3fb0-7e36-588f-9f4a-f84b7768c84c
-- title:
--   Relations in Pic⁰ make geometric cycles principal
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $F$ a $K$-algebra which is a field satisfying `IsCurveOver K F` (every nonzero element of $F$ has a degree-zero divisor recording its orders at all places, each residue field is finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$), and assume some $x \in F$ is transcendental over $K$ with $F$ finite over $K(x)$. Let $(F' i)_{i \in \iota}$ be fields over $K$ each having principal divisors, and $\varphi_i, \psi_i \colon F \to F' i$ two $K$-algebra maps whose underlying ring maps are integral, with `FundamentalIdentityAlong` holding along each $\varphi_i$, each $F' i$ module-finite over $F$ along $\psi_i$, and the pushforward norm formula `NormFormulaAlong` holding along each $\psi_i$; these hypotheses make $T_i := \psi_{i*} \circ \varphi_i^{*}$ an endomorphism `Pic0.correspondence` of $\mathrm{Pic}^0(F/K)$. Let $p$ be an element of the free $\mathbb{Z}$-algebra on $\iota$ and suppose that the image of $p$ under the lift sending $i$ to $T_i$ (as a $\mathbb{Z}$-linear endomorphism) is $0$. Let $E$ be an algebraically closed field over $K$ and $FE$ a field with compatible $E$- and $F$-algebra structures over $K$, satisfying `IsCurveOver E FE`, finite over $E(x)$ for some $x \in FE$ transcendental over $E$, and generated over $E$ by the image of $F$; let $\eta \colon F \to E$ be a $K$-algebra map. Then there exist a nonzero $g \in FE$, a finite set $S$ of places of $FE$ over $E$, and an assignment $y$ of a $K$-algebra map $F \to E$ to each place, such that: every $P \in S$ satisfies $v_P(f - y_P(f)) < 1$ for all $f \in F$ (the images in $FE$ being understood), that is, $P$ is centred at the geometric point $y_P$; every $P \notin S$ at which $g$ has nonzero order admits an $f \in F$ whose image lies outside the valuation subring of $P$; and, in the free abelian group on $\mathrm{Hom}_K(F,E)$, the cycle $\sum_{P \in S} \mathrm{ord}_P(g)\,[y_P]$ equals the image of $[\eta]$ under the image of $p$ by the lift sending $i$ to the additive endomorphism determined by $[e] \mapsto \sum_{\sigma \colon F' i \to E,\ \sigma \circ \varphi_i = e} [\sigma \circ \psi_i]$.
--
--   This is the rigidity half of the faithfulness of the action of correspondences: a noncommutative polynomial in the $T_i$ which annihilates $\mathrm{Pic}^0(F/K)$ over the algebraically closed base $K$ still annihilates classes after constant-field extension to $E$, so that the $0$-cycle $p \cdot [\eta]$ of geometric points becomes, up to places where $F$ is not regular, the divisor of a function on $FE$. It feeds the companion statement that $p$ then also annihilates the action of the correspondences on $\Omega[F/K]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (η : F →ₐ[K] E) :
    ∃ (g : FE) (_ : g ≠ 0) (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E)),
      (∀ P ∈ S, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1) ∧
      (∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
        ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) ∧
      (∑ P ∈ S, Finsupp.single (y P) (P.ord g) : (F →ₐ[K] E) →₀ ℤ) =
        FreeAlgebra.lift ℤ (fun i => (Finsupp.liftAddHom fun e : F →ₐ[K] E =>
          zmultiplesHom ((F →ₐ[K] E) →₀ ℤ)
            (∑ᶠ σ ∈ {σ : F' i →ₐ[K] E | σ.comp (φ i) = e},
              Finsupp.single (σ.comp (ψ i)) (1 : ℤ))).toIntLinearMap) p (Finsupp.single η 1) := by sorry
