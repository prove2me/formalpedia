-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:02.12206+00:00
-- url     : https://prove2.me/submissions/d222c8cc-aa2f-478b-a3eb-a27c0c4fe892

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
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
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
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
  have hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox
    exact Metric.self_subset_thickening (by
      unfold smoothApproxRadius
      positivity) _
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase_radial_positiveDegree
      A Omega hcarrier hCauchyP hsupport hkernel hphaseNormalized
  · intro p n hp
    let q := p - Polynomial.C (Polynomial.eval 0 p)
    have hqdegree : 0 < q.natDegree := by
      simpa only [q, Polynomial.natDegree_sub_C] using hp
    have hqzero : Polynomial.eval 0 q = 0 := by
      simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
    have hqapprox := happrox q n hqdegree hqzero
    have hS : compactThickeningApprox (closure (numericalRange A)) n ⊆
        closure (Omega n).carrier := by
      rw [hclosure n]
    have htransfer :=
      exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
        (Omega n) q (Polynomial.eval 0 p) (hkernel n)
        (compactThickeningApprox (closure (numericalRange A)) n) hS
        (fun j => 1 / ((j : ℝ) + 1)) hqapprox
    have hqadd : q + Polynomial.C (Polynomial.eval 0 p) = p := by
      dsimp only [q]
      abel
    rw [hqadd] at htransfer
    exact htransfer
  · intro p n _hp
    exact
      crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
        A (Omega n) (hOmega n) (hkernel n)
          (fun q hq hqzero hqnorm => hPlemelj q n hq hqzero hqnorm) p
