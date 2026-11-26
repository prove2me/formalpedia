-- Prove2me | solution 1 for exists_polynomial_rate_approximation_of_tendstoUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:06.761896+00:00
-- url     : https://prove2.me/submissions/5079a325-cc81-4acb-885e-aaa4c8b7e763

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
theorem _root_.solution
    (K : Set ℂ) (f : ℂ → ℂ) (q : ℕ → Polynomial ℂ)
    (hlim : TendstoUniformlyOn
      (fun j z ↦ Polynomial.eval z (q j)) f atTop K) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ K →
        ‖Polynomial.eval z (r j) - f z‖ ≤ 1 / ((j : ℝ) + 1) := by
  have hevent : ∀ j : ℕ, ∀ᶠ k in atTop,
      ∀ z ∈ K,
        dist (f z) (Polynomial.eval z (q k)) < 1 / ((j : ℝ) + 1) := by
    intro j
    apply (Metric.tendstoUniformlyOn_iff.mp hlim)
    positivity
  choose N hN using fun j ↦ (eventually_atTop.1 (hevent j))
  refine ⟨fun j ↦ q (N j), ?_⟩
  intro j z hz
  have hlt := hN j (N j) le_rfl z hz
  rw [dist_eq_norm] at hlt
  simpa only [norm_sub_rev] using hlt.le
