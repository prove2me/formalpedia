-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:05.199592+00:00
-- url     : https://prove2.me/submissions/bfc99ef7-6c5f-421d-b19b-188d2a57e591

import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Theorems.Thm_exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_continuous_scalar_companion_approximation
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
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
    (hreg : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized (Omega n) p xi)
        (nhdsWithin xi (Omega n).carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized
            (Omega n) p xi xi)))
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    simpa only [K] using hbounded.isCompact_closure
  have hstageBounded : ∀ n, Bornology.IsBounded (Omega n).carrier := by
    intro n
    rw [hcarrier n]
    exact hKcompact.isBounded.thickening
  have hclosure : ∀ n,
      closure (Omega n).carrier = compactThickeningApprox K n := by
    intro n
    rw [hcarrier n]
    unfold convexThickeningApprox compactThickeningApprox
    exact closure_thickening (by
      unfold smoothApproxRadius
      positivity) K
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_continuous_scalar_companion_approximation
      A Omega hcarrier hCauchyP hsupport
  intro p n
  obtain ⟨r, hr⟩ := happrox p n
  have hr' : ∀ (j : ℕ) (z : ℂ), z ∈ closure (Omega n).carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p z‖ ≤
        1 / ((j : ℝ) + 1) := by
    intro j z hz
    apply hr j z
    simpa only [K, ← hclosure n] using hz
  obtain ⟨g, q, hgcont, hgbound, hqapprox, hgaux⟩ :=
    exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
      A (Omega n) p (hstageBounded n) (hkernel n)
        (hreg p n) (hphase p n) r hr' (hPlemelj p n)
  refine ⟨g, q, hgcont, ?_, ?_, hgaux⟩
  · intro z hz
    change z ∈ compactThickeningApprox K n at hz
    rw [← hclosure n] at hz
    have hg := hgbound z hz
    rw [hclosure n] at hg
    simpa only [K] using hg
  · intro j z hz
    change z ∈ compactThickeningApprox K n at hz
    rw [← hclosure n] at hz
    exact hqapprox j z hz
