-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm
-- name    : AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/eb5773da-d8e7-5596-8ca4-f2ce06726830
-- title:
--   Conorm map on Pic⁰ intertwines correspondence operators
-- statement:
--   Let $K, F, F', E, F_E, F'_E$ be fields with $F,F',E$ algebras over $K$, $F_E$ an algebra over $E$, $F$ and $K$, and $F'_E$ an algebra over $E$, $F'$ and $K$, all compatibly (scalar towers over $K$), with $K$ algebraically closed of characteristic zero and $E$ algebraically closed. Each of $F,F'$ (over $K$) and $F_E,F'_E$ (over $E$) is assumed to contain a transcendental element over which it is finite-dimensional, and each is a curve in the project's sense: every nonzero function has a divisor of degree zero recording its orders at all places, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one. Further, $F_E$ is generated over $E$ by the image of $F$, and $F'_E$ by the image of $F'$, and $F'$ over $K$, $F'_E$ over $E$ have principal divisors. Given $K$-algebra maps $\varphi,\psi\colon F\to F'$ and $E$-algebra maps $\varphi_E,\psi_E\colon F_E\to F'_E$, all integral as ring maps, with $\varphi_E,\psi_E$ extending $\varphi,\psi$ along the maps $F\to F_E$, $F'\to F'_E$, and given the inputs making the correspondences $T=\psi_*\varphi^*$ on $\mathrm{Pic}^0(F/K)$ and $T_E=(\psi_E)_*(\varphi_E)^*$ on $\mathrm{Pic}^0(F_E/E)$ available (`FundamentalIdentityAlong` along $\varphi$ and $\varphi_E$; finiteness of $F'$ over $F$ along $\psi$ and of $F'_E$ over $F_E$ along $\psi_E$, with the corresponding `NormFormulaAlong` pushforward norm formulae), let $\iota\colon\mathrm{Pic}^0(F/K)\to\mathrm{Pic}^0(F_E/E)$ be an additive map subject to two conditions: $\iota[D]=[D']$ whenever the degree-zero divisor $D'$ on $F_E$ takes the value $D(v)$ at every place $v'$ whose valuation subring pulls back along $F\to F_E$ to that of $v$, and vanishes at every place $v'$ pulling back to no place of $F$; and such a $D'$ exists for every degree-zero $D$. Then $\iota(Tx)=T_E(\iota x)$ for all $x\in\mathrm{Pic}^0(F/K)$.
--
--   This is the compatibility of the conorm (constant field extension) map on degree-zero divisor class groups with the correspondence operators $\psi_*\varphi^*$ attached to a pair of integral maps of function fields; the map $\iota$ is characterised axiomatically through conorm divisors rather than constructed. It supplies the Hecke-equivariance half of the comparison of Jacobians used in the construction of Shimura curve models with good reduction in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm
    (K F F' E FE F'E : Type*) [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE : ∃ x : FE, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hfgE' : ∃ x : F'E, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F'] [AlgebraicCurve.IsCurveOver E FE] [AlgebraicCurve.IsCurveOver E F'E]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    [AlgebraicCurve.HasPrincipalDivisors K F'] [AlgebraicCurve.HasPrincipalDivisors E F'E]
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hcommφ : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hcommψ : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))

    (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hFIE : AlgebraicCurve.FundamentalIdentityAlong E φE hφE) (hfinE : AlgebraicCurve.FiniteAlong E ψE)
    (hNE : AlgebraicCurve.NormFormulaAlong E ψE hfinE)

    (ι : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 E FE)
    (hpin : ∀ (D : AlgebraicCurve.Divisor.degZero (K := K) (F := F)) (D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE)),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) →
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0) →
      ι (AlgebraicCurve.Pic0.mk D) = AlgebraicCurve.Pic0.mk D')
    (hex : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F), ∃ D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) ∧
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0)) :
    ∀ x : AlgebraicCurve.Pic0 K F,
      ι (AlgebraicCurve.Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) =
        AlgebraicCurve.Pic0.correspondence φE ψE hφE hψE hFIE hfinE hNE (ι x) := by sorry
