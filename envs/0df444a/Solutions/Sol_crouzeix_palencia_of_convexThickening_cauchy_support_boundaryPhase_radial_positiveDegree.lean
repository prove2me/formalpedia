-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_positiveDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:04.670337+00:00
-- url     : https://prove2.me/submissions/3bfd67dc-c8cf-4bf6-a1a9-0f5f714aea17

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_approximation
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
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
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : Set ℂ := closure (numericalRange A)
  have hclosure : ∀ n,
      closure (Omega n).carrier = compactThickeningApprox K n := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox compactThickeningApprox
    exact closure_thickening (by
      unfold smoothApproxRadius
      positivity) K
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_approximation
      A Omega hcarrier hCauchyP hsupport hkernel hphase
  · intro p n
    by_cases hp : 0 < p.natDegree
    · exact happrox p n hp
    · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
      let a := p.coeff 0
      have hpC : p = Polynomial.C a :=
        Polynomial.eq_C_of_natDegree_eq_zero hpzero
      rw [hpC]
      refine ⟨fun _ => Polynomial.C (star a), ?_⟩
      intro j z hz
      have hzclosure : z ∈ closure (Omega n).carrier := by
        rw [hclosure n]
        simpa only [K] using hz
      rw [Polynomial.eval_C,
        crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
          (Omega n) a (hkernel n) hzclosure,
        sub_self, norm_zero]
      positivity
  · intro p n
    by_cases hp : 0 < p.natDegree
    · exact hPlemelj p n hp
    · have hpzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hp
      let a := p.coeff 0
      have hpC : p = Polynomial.C a :=
        Polynomial.eq_C_of_natDegree_eq_zero hpzero
      rw [hpC]
      exact
        crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
          A (Omega n) a (hkernel n)
