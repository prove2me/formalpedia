-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:56:00.035596+00:00
-- url     : https://prove2.me/submissions/e11cfe92-9720-4ddb-a006-c0109c723084

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
import Theorems.Thm_exists_global_polynomial_calculus_bound_frontier_of_cauchy
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
import Theorems.Thm_polynomialSupNorm_mono_of_isCompact
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfrontier : ∀ n, frontier (Omega n).carrier ⊆ K n)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
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
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hCauchy : ∀ n : ℕ,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := fun n =>
    contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
      A (Omega n) (fun p => hCauchyP p n)
  have hCauchyOne : ∀ n : ℕ,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        deriv (Omega n).boundaryParam t •
          resolvent A ((Omega n).boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
    intro n
    simpa only [contourIntegral, one_smul] using hCauchy n
  have hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p (K n) := by
    intro n
    obtain ⟨C, hC, hbound⟩ :=
      exists_global_polynomial_calculus_bound_frontier_of_cauchy
        A (Omega n) (hOmega n) (fun p => hCauchyP p n)
    refine ⟨C, hC, ?_⟩
    intro p
    exact (hbound p).trans (mul_le_mul_of_nonneg_left
      (polynomialSupNorm_mono_of_isCompact p (hfrontier n) (hcompact n)) hC)
  apply crouzeix_palencia_of_antitone_compact_tendsto_polynomial_companions
    A K hanti hcompact hnonempty hinter hfinite
  intro p n
  obtain ⟨q, hq, hqLim⟩ := hcompanion p n
  refine ⟨crouzeixPolynomialAuxiliaryOperator A (Omega n) p,
    q, hq, hqLim, ?_⟩
  exact
    norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_le_two_mul_polynomialSupNorm_of_frontier_subset_of_cauchy_support
      A (Omega n) p (K n) (hcompact n) (hfrontier n) (hOmega n)
        (hCauchyP p n) (hCauchyOne n) (hsupport n)
