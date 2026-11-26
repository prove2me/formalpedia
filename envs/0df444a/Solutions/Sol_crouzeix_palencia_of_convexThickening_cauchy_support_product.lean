-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:37.51216+00:00
-- url     : https://prove2.me/submissions/b976f498-1142-4ae9-8ed7-4ebf17460c28

import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
import Theorems.Thm_convexThickeningApprox_spec
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_crouzeix_palencia_of_compactThickening_auxiliary_bounds
import Theorems.Thm_frontier_convexThickeningApprox_subset_compactThickeningApprox
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
import Theorems.Thm_norm_le_of_mem_numericalRange
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
    (hprod : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p‖ ≤
        polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hCauchy : ∀ n : ℕ,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := fun n ↦
    contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
      A (Omega n) (fun p ↦ hCauchyP p n)
  have hCauchyOne : ∀ n : ℕ,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (Omega n).boundaryParam t •
          resolvent A ((Omega n).boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    intro n
    simpa only [contourIntegral, one_smul] using hCauchy n
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_closure_numericalRange_smoothApproximation A
  have hKconvex : Convex ℝ K := by
    simpa only [K] using (convex_numericalRange A).closure
  have hstageCompact : ∀ n, IsCompact (compactThickeningApprox K n) :=
    fun _ ↦ hKcompact.cthickening
  apply crouzeix_palencia_of_compactThickening_auxiliary_bounds A
  intro p n
  refine ⟨crouzeixPolynomialAuxiliaryOperator A (Omega n) p, ?_, ?_⟩
  · apply
      norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
        A (Omega n) p (compactThickeningApprox K n) (hstageCompact n)
    · rw [hcarrier n]
      exact frontier_convexThickeningApprox_subset_compactThickeningApprox K n
    · rw [hcarrier n]
      exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
    · exact hCauchyP p n
    · exact hCauchyOne n
    · intro t ht w hw
      exact hsupport n t ht w hw
  · by_cases hp : p.natDegree = 0
    · rcases subsingleton_or_nontrivial E with hE | hE
      · let _ := hE
        have hzero : Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A (Omega n) p = 0 :=
          Subsingleton.elim _ _
        rw [hzero, norm_zero]
        exact sq_nonneg _
      · let _ := hE
        obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
          NormedSpace.sphere_nonempty.mpr zero_le_one
        have hxnorm : ‖x‖ = 1 := by
          rw [Metric.mem_sphere, dist_zero_right] at hx
          exact hx
        have hW : (numericalRange A).Nonempty :=
          ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
        have hKnonempty : K.Nonempty := by
          simpa only [K] using hW.mono subset_closure
        have hstageNonempty :
            (compactThickeningApprox K n).Nonempty :=
          hKnonempty.mono
            (Metric.self_subset_cthickening
              (E := K) (δ := smoothApproxRadius n))
        exact
          norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
            A (Omega n) p hstageNonempty hp (hCauchy n)
    · simpa only [K] using hprod p n (Nat.pos_of_ne_zero hp)
