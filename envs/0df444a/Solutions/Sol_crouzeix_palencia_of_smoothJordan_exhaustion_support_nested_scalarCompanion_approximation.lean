-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordan_exhaustion_support_nested_scalarCompanion_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:40.289797+00:00
-- url     : https://prove2.me/submissions/6843079d-8f01-472b-a856-de8f1fa1887f

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
import Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_frontier_infinite
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_canonicalNormal_support_all_of_Ioc
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
import Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
import Theorems.Thm_exists_tendsto_polynomial_companions_of_uniform_approximation
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
import Theorems.Thm_polynomialSupNorm_closure_carrier_eq_frontier
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
import Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
import Theorems.Thm_spectrum_subset_closure_numericalRange
import Theorems.Thm_tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
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
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
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
    have hmass : ∀ n,
        contourIntegral (resolvent A) (Omega n).boundaryParam =
          (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
      intro n
      exact
        contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
          A (Omega n) c (horiented n).1 (horiented n).2 (hOmega n)
    have hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
        Polynomial.aeval A p =
          (2 * (Real.pi : ℂ) * I)⁻¹ •
            contourIntegral
              (fun z => Polynomial.eval z p • resolvent A z)
              (Omega n).boundaryParam := by
      intro p n
      exact polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
        A (Omega n) (hOmega n) (hmass n) p
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_cauchy_support_tendsto_polynomial_companions
        A Omega K hanti hcompact hnonempty hinter
    · intro n
      rw [hK n]
      exact frontier_subset_closure
    · exact hOmega
    · exact hCauchyP
    · exact hsupport
    · intro p n
      have hkernel : ∀ z ∈ (Omega n).carrier,
          crouzeixScalarCauchyKernel (Omega n) z = 1 :=
        crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
          (Omega n) c (horiented n).1 (horiented n).2
      have hphase : CrouzeixBoundaryPhaseContractive (Omega n) p :=
        crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
          (Omega n) c (horiented n).1 (horiented n).2 p
      obtain ⟨r, hr⟩ := happrox p n
      let g : ℂ → ℂ :=
        crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p
      have hbounded : Bornology.IsBounded (Omega n).carrier :=
        (Omega n).isBounded_carrier_of_cauchyKernel_eq_one hkernel
      have hgcontOuter : ContinuousOn g (closure (Omega n).carrier) := by
        dsimp only [g]
        exact
          continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
            (Omega n) p hbounded hkernel
      have hgcontInner : ContinuousOn g
          ((Omega (n + 1)).boundaryParam ''
            Icc (0 : ℝ) (2 * Real.pi)) := by
        apply hgcontOuter.mono
        rintro z ⟨t, _ht, rfl⟩
        apply subset_closure
        apply hnest n
        apply frontier_subset_closure
        rw [← (Omega (n + 1)).boundaryParam_range]
        exact mem_range_self t
      have hgbound : ∀ z ∈ K n,
          ‖g z‖ ≤ polynomialSupNorm p (K n) := by
        intro z hz
        have hzclosure : z ∈ closure (Omega n).carrier := by
          rwa [← hK n]
        calc
          ‖g z‖ ≤ polynomialSupNorm p (frontier (Omega n).carrier) := by
            dsimp only [g]
            exact
              norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
                (Omega n) p hkernel hphase hzclosure
          _ = polynomialSupNorm p (closure (Omega n).carrier) :=
            (polynomialSupNorm_closure_carrier_eq_frontier
              (Omega n) p hbounded).symm
          _ = polynomialSupNorm p (K n) := by rw [hK n]
      have hboundaryApprox : ∀ (j : ℕ) (t : ℝ),
          t ∈ Icc (0 : ℝ) (2 * Real.pi) →
          ‖Polynomial.eval ((Omega (n + 1)).boundaryParam t) (r j) -
            g ((Omega (n + 1)).boundaryParam t)‖ ≤
              1 / ((j : ℝ) + 1) := by
        intro j t _ht
        apply hr j
        rw [hK n]
        apply subset_closure
        apply hnest n
        apply frontier_subset_closure
        rw [← (Omega (n + 1)).boundaryParam_range]
        exact mem_range_self t
      have hlim :=
        tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
          A (Omega (n + 1)) g r (hOmega (n + 1)) hgcontInner
            (fun j => hCauchyP (r j) (n + 1)) hboundaryApprox
      have haux : crouzeixAuxiliaryOperator A (Omega (n + 1)) g =
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p := by
        dsimp only [g]
        exact
          crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
            A (Omega (n + 1)) (Omega n) p (hOmega (n + 1))
              (hmass (n + 1)) (hnest n)
      have hlim' : Tendsto (fun j => Polynomial.aeval A (r j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p)) := by
        simpa only [haux] using hlim
      apply exists_tendsto_polynomial_companions_of_uniform_approximation
        A (K n) (polynomialSupNorm p (K n))
          (polynomialSupNorm_nonneg p (K n)) g hgbound
          (crouzeixPolynomialAuxiliaryOperator A (Omega n) p) ?_ r ?_ hlim'
      · intro hm
        have hpzero : p = 0 :=
          polynomial_eq_zero_of_polynomialSupNorm_eq_zero p (hcompact n)
            ((Omega n).frontier_infinite.mono (by
              rw [hK n]
              exact frontier_subset_closure)) hm
        subst p
        calc
          crouzeixPolynomialAuxiliaryOperator A (Omega n) 0 =
              crouzeixPolynomialAuxiliaryOperator A (Omega n)
                (0 • (1 : Polynomial ℂ)) := by rw [zero_smul]
          _ = star (0 : ℂ) •
              crouzeixPolynomialAuxiliaryOperator A (Omega n) 1 :=
            crouzeixPolynomialAuxiliaryOperator_smul A (Omega n) 0 1
          _ = 0 := by simp only [star_zero, zero_smul]
      · intro j z hz
        exact hr j z hz
