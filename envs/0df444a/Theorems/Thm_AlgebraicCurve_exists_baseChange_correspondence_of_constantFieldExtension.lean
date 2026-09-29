-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
-- name    : AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/17e7ae5b-4250-5a60-8aad-ec5a056e5d03
-- title:
--   Base change of a curve correspondence to a constant field extension
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a $K$-algebra which is a field satisfying `IsCurveOver K F` (every nonzero $f \in F$ has a divisor of degree $0$ recording its orders at all places, every place of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$), and assume $F$ contains an element $x$ transcendental over $K$ with $F$ finite over $K(x)$. Let $F'$ be a field extension of $K$ in which every nonzero element has a degree-zero divisor (`HasPrincipalDivisors K F'`), and let $\varphi, \psi \colon F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, such that the fundamental identity holds for $F'$ over $F$ via $\varphi$, $F'$ is a finite $F$-module via $\psi$, and the pushforward norm formula holds along $\psi$. Let $E$ be an algebraically closed extension field of $K$ and $FE$ a field which is an $E$-algebra and an $F$-algebra, compatibly over $K$, with `IsCurveOver E FE`, containing an element transcendental over $E$ with $FE$ finite over the subfield it generates, and with $FE$ generated over $E$ by the image of $F$. Then there is a field $F'E$, an $E$-algebra and an $F'$-algebra compatibly over $K$, with `IsCurveOver E F'E`, together with $E$-algebra maps $\varphi_E, \psi_E \colon FE \to F'E$ with integral underlying ring homomorphisms, satisfying the fundamental identity along $\varphi_E$, finiteness of $F'E$ over $FE$ along $\psi_E$ and the norm formula along $\psi_E$, such that: $F'E$ contains an element transcendental over $E$ over which it is finite; $F'E$ is generated over $E$ by the image of $F'$; $\varphi_E$ and $\psi_E$ restrict along $F \to FE$ to $\varphi$ and $\psi$ followed by $F' \to F'E$; and, writing $T_E = \psi_{E*} \circ \varphi_E^{*}$ for `Divisor.correspondence φE ψE hφE hψE` on divisors of $FE/E$ and calling a place $P$ of $FE/E$ (a proper valuation subring of $FE$ containing $E$ whose valuation ring is a principal ideal ring) centred at $e \in \mathrm{Hom}_K(F,E)$ when $v_P(f - e(f)) < 1$ for all $f \in F$: (i) if $P$ is centred at $e$ and $Q$ at $e'$, the coefficient of $Q$ in $T_E(\mathrm{single}\,P\,1)$ equals the value at $e'$ of the finite sum $\sum_{\sigma \colon \sigma \circ \varphi = e} \mathrm{single}\,(\sigma \circ \psi)\,1$ over $\sigma \in \mathrm{Hom}_K(F',E)$, i.e. the number of $\sigma$ with $\sigma \circ \varphi = e$ and $\sigma \circ \psi = e'$; (ii) if $P$ is centred at some $e$ and $Q$ occurs with nonzero coefficient in $T_E(\mathrm{single}\,P\,1)$, then $Q$ is centred at some $e' \in \mathrm{Hom}_K(F,E)$; (iii) if some element of $F$ maps outside the valuation subring of $P$ and $Q$ occurs with nonzero coefficient in $T_E(\mathrm{single}\,P\,1)$, then some element of $F$ maps outside the valuation subring of $Q$.
--
--   This is the classical statement that a correspondence $(\varphi,\psi)$ on a curve over $K$ base changes to the constant field extension of the curve and of its roof to an algebraically closed $E \supseteq K$, together with the fibre formula expressing the multiplicities of the base-changed correspondence at places centred at $K$-embeddings $F \to E$ in terms of embeddings of the roof. It is used in the treatment of the induced action on $\mathrm{Pic}^0$ and on Tate modules, for instance by [`AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map`](thm.html#AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map) and by the $\mathrm{Pic}^0$ statements on lifted correspondences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u v w x

theorem AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type w) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E : Type x) (FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    ∃ (F'E : Type (max w x)) (_ : Field F'E) (_ : Algebra E F'E) (_ : Algebra F' F'E)
      (_ : Algebra K F'E) (_ : IsScalarTower K E F'E) (_ : IsScalarTower K F' F'E)
      (_ : IsCurveOver E F'E)
      (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
      (_ : FundamentalIdentityAlong E φE hφE) (hfinE : FiniteAlong E ψE)
      (_ : NormFormulaAlong E ψE hfinE),
      (∃ x' : F'E, Transcendental E x' ∧
        FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E) ∧
      IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤ ∧
      (∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f)) ∧
      (∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f)) ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ (Q : Place E FE) (e' : F →ₐ[K] E),
        (∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) →
          Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q =
            (∑ᶠ σ ∈ {σ : F' →ₐ[K] E | σ.comp φ = e},
              Finsupp.single (σ.comp ψ) (1 : ℤ) : (F →ₐ[K] E) →₀ ℤ) e') ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ e' : F →ₐ[K] E, ∀ f : F,
            Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) ∧
      (∀ P : Place E FE, (∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring) := by sorry
