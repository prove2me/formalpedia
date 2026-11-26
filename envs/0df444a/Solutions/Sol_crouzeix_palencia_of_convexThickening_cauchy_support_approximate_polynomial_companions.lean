-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_approximate_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:22.275978+00:00
-- url     : https://prove2.me/submissions/d7375d01-35de-46da-a108-18aa4b75bc01

import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
import Theorems.Thm_compactThickeningApprox_infinite
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_exists_tendsto_polynomial_companions_of_add_one_div_bounds
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
import Theorems.Thm_spectrum_subset_closure_numericalRange
attribute [local simp] mem_numericalRange


section
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private theorem isCompact_closure_numericalRange_smoothApproximation
    (A : E →L[ℂ] E) : IsCompact (closure (numericalRange A)) := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact hbounded.isCompact_closure
variable [CompleteSpace E]
end

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (r j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
              (compactThickeningApprox (closure (numericalRange A)) n) +
            1 / ((j : ℝ) + 1)) ∧
        Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    constructor
    · exact spectrum_subset_closure_numericalRange A
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (polynomialSupNorm_nonneg p (closure (numericalRange A)))
  · let _ := hE
    let K : Set ℂ := closure (numericalRange A)
    have hKcompact : IsCompact K := by
      simpa only [K] using
        isCompact_closure_numericalRange_smoothApproximation A
    have hKnonempty : K.Nonempty := by
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      simpa only [K] using hW.mono subset_closure
    apply
      crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
        A Omega hcarrier hCauchyP hsupport
    intro p n
    obtain ⟨r, hr, hrlim⟩ := hcompanion p n
    apply exists_tendsto_polynomial_companions_of_add_one_div_bounds
      A (compactThickeningApprox K n) (polynomialSupNorm p
        (compactThickeningApprox K n))
      (polynomialSupNorm_nonneg p (compactThickeningApprox K n))
      (crouzeixPolynomialAuxiliaryOperator A (Omega n) p)
    · intro hm
      have hp : p = 0 :=
        polynomial_eq_zero_of_polynomialSupNorm_eq_zero p
          (hKcompact.cthickening : IsCompact (compactThickeningApprox K n))
          (compactThickeningApprox_infinite K n hKnonempty) hm
      subst p
      calc
        crouzeixPolynomialAuxiliaryOperator A (Omega n) 0 =
            crouzeixPolynomialAuxiliaryOperator A (Omega n)
              (0 • (1 : Polynomial ℂ)) := by rw [zero_smul]
        _ = star (0 : ℂ) •
            crouzeixPolynomialAuxiliaryOperator A (Omega n) 1 :=
          crouzeixPolynomialAuxiliaryOperator_smul A (Omega n) 0 1
        _ = 0 := by simp only [star_zero, zero_smul]
    · simpa only [K] using hr
    · simpa only [K] using hrlim
