-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordan_exhaustion_support_scalarCompanion_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:00.654411+00:00
-- url     : https://prove2.me/submissions/01cb9859-4293-464c-a76d-26d825164a2a

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
import Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_support_scalarCompanion_approximation
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_canonicalNormal_support_all_of_Ioc
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
import Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_spectrum_subset_closure_numericalRange
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
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
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
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    have horiented : ∀ n, c ∈ (Omega n).carrier ∧ ∀ t : ℝ,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (c - (Omega n).boundaryParam t)).re ≤ 0 := by
      intro n
      refine ⟨hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    have hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
        crouzeixScalarCauchyKernel (Omega n) z = 1 := by
      intro n
      exact crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
        (Omega n) c (horiented n).1 (horiented n).2
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_support_scalarCompanion_approximation
        A Omega K hanti hcompact hnonempty hinter hK hOmega hsupport
    · intro p n
      by_cases hp : 0 < p.natDegree
      · let q := p - Polynomial.C (Polynomial.eval 0 p)
        have hqdegree : 0 < q.natDegree := by
          simpa only [q, Polynomial.natDegree_sub_C] using hp
        have hqzero : Polynomial.eval 0 q = 0 := by
          simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
        have hqapprox := happrox q n hqdegree hqzero
        have hS : K n ⊆ closure (Omega n).carrier := by
          intro z hz
          simpa only [hK n] using hz
        have htransfer :=
          exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
            (Omega n) q (Polynomial.eval 0 p) (hkernel n)
            (K n) hS (fun j => 1 / ((j : ℝ) + 1)) hqapprox
        have hqadd : q + Polynomial.C (Polynomial.eval 0 p) = p := by
          dsimp only [q]
          abel
        rw [hqadd] at htransfer
        exact htransfer
      · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
        let a := p.coeff 0
        have hpC : p = Polynomial.C a :=
          Polynomial.eq_C_of_natDegree_eq_zero hpzero
        rw [hpC]
        refine ⟨fun _ => Polynomial.C (star a), ?_⟩
        intro j z hz
        have hzclosure : z ∈ closure (Omega n).carrier := by
          simpa only [hK n] using hz
        rw [Polynomial.eval_C,
          crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
            (Omega n) a (hkernel n) hzclosure,
          sub_self, norm_zero]
        positivity
    · intro p n
      exact
        crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
          A (Omega n) (hOmega n) (hkernel n)
            (fun q hq hqzero hqnorm => hPlemelj q n hq hqzero hqnorm) p
