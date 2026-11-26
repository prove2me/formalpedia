-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:10.228526+00:00
-- url     : https://prove2.me/submissions/9291c5fd-4ce5-49d8-9198-5ebb1fd0430d

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
import Theorems.Thm_crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
import Theorems.Thm_exists_global_polynomial_calculus_bound_frontier_of_cauchy
import Theorems.Thm_frontier_convexThickeningApprox_subset_compactThickeningApprox
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_mono_of_isCompact
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
      ∃ q : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (q j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
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
  have hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        C * polynomialSupNorm p (compactThickeningApprox K n) := by
    intro n
    have hOmega : K ⊆ (Omega n).carrier := by
      rw [hcarrier n]
      exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
    obtain ⟨C, hC, hbound⟩ :=
      exists_global_polynomial_calculus_bound_frontier_of_cauchy
        A (Omega n) hOmega (fun p ↦ hCauchyP p n)
    refine ⟨C, hC, ?_⟩
    intro p
    calc
      ‖Polynomial.aeval A p‖ ≤
          C * polynomialSupNorm p (frontier (Omega n).carrier) := hbound p
      _ ≤ C * polynomialSupNorm p (compactThickeningApprox K n) :=
        mul_le_mul_of_nonneg_left
          (polynomialSupNorm_mono_of_isCompact p (by
            rw [hcarrier n]
            exact frontier_convexThickeningApprox_subset_compactThickeningApprox K n)
            (hstageCompact n)) hC
  apply crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
    A (by simpa only [K] using hfinite)
  intro p n
  obtain ⟨q, hq, hq_lim⟩ := hcompanion p n
  refine ⟨crouzeixPolynomialAuxiliaryOperator A (Omega n) p,
    q, hq, hq_lim, ?_⟩
  apply
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
      A (Omega n) p
      (compactThickeningApprox (closure (numericalRange A)) n)
      (by simpa only [K] using hstageCompact n)
  · rw [hcarrier n]
    exact frontier_convexThickeningApprox_subset_compactThickeningApprox
      (closure (numericalRange A)) n
  · rw [hcarrier n]
    exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
  · exact hCauchyP p n
  · exact hCauchyOne n
  · intro t ht w hw
    exact hsupport n t ht w hw
