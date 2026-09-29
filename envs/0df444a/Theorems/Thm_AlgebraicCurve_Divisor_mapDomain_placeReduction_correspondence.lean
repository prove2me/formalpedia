-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence
-- name    : AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/4e067962-c098-5c3e-96b1-ccd66c92bbf9
-- title:
--   Constant reduction commutes with a correspondence and its base change
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $F$ a $K$-algebra which is a field and a curve over $K$ in the project's sense (every nonzero element has a divisor of degree $0$ recording its orders at all places, every place has residue field finite over $K$, and $\Omega[F/K]$ is free of rank $1$ over $F$), with $F$ finite over $K(x)$ for some transcendental $x$; here a place of $F/K$ is a valuation subring, distinct from $F$, containing $K$ and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $F'/K$ be a field with principal divisors and $\varphi,\psi : F \to F'$ two integral $K$-algebra maps, such that the fundamental identity holds along $\varphi$, $F'$ is a finite $F$-module along $\psi$, and the pushforward norm formula holds along $\psi$; the associated correspondence on divisors of $F/K$ is $\psi_* \circ \varphi^*$. Let $E \supseteq K$ be algebraically closed, $FE$ a curve over $E$ containing $F$ compatibly, finitely generated in the above sense and generated over $E$ by the image of $F$, and similarly $F'E$ a curve over $E$ generated over $E$ by the image of $F'$, with $K$-compatible towers. Let $\varphi_E,\psi_E : FE \to F'E$ be $E$-algebra maps extending $\varphi,\psi$ (i.e. agreeing with them on the image of $F$ after composing with $F' \to F'E$), both integral, with the fundamental identity along $\varphi_E$ and finiteness and the norm formula along $\psi_E$, giving the correspondence $\psi_{E*} \circ \varphi_E^*$ on divisors of $FE/E$. Let $A$ be a valuation subring of $E$ containing the image of $K$ such that every $a \in A$ satisfies $v_A(a - k) < 1$ for some $k \in K$, and let $r$ be a map from places of $FE/E$ to places of $F/K$ such that for every place $P$ and every $f \in F$, $f$ lies in the valuation subring of $r(P)$ if and only if the image of $f$ in $FE$ is congruent to the image of some $a \in A$ modulo the maximal ideal of $P$. Then for every divisor $D$ of $FE/E$, pushing $\psi_{E*}\varphi_E^* D$ forward along $r$ (by `Finsupp.mapDomain`) gives the same divisor of $F/K$ as applying $\psi_* \circ \varphi^*$ to the pushforward of $D$ along $r$.
--
--   This is the compatibility of Deuring's constant reduction of divisors, taken along a $K$-rational place $A$ of the constant field $E$, with a correspondence defined over $K$ and its base change to $E$: reduction of places is equivariant for pullback along $\varphi$ and pushforward along $\psi$. It is used in the two statements [`AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero`](thm.html#AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero) and [`AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange`](thm.html#AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange), which transfer the vanishing of a correspondence action on degree-zero divisor classes between a curve and its algebraically closed constant-field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (hfinE : FiniteAlong E ψE) (hNE : NormFormulaAlong E ψE hfinE)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (D : Divisor E FE) :
    Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE D) =
      Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r D) := by sorry
