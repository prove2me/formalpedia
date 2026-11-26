-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_support_nested_scalarCompanion_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:25.069092+00:00
-- url     : https://prove2.me/submissions/b25ae143-f7d5-4bb2-9ed7-d48f72fc3b2a

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_support_nested_scalarCompanion_radial_vanishingAtZero
import Theorems.Thm_closure_convexThickeningApprox_succ_subset
import Theorems.Thm_compactThickeningApprox_spec
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_spectrum_subset_closure_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
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
    have hcompact : IsCompact (closure (numericalRange A)) := by
      have hbounded : Bornology.IsBounded (numericalRange A) :=
        Metric.isBounded_closedBall.subset (fun z hz ↦ by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact norm_le_of_mem_numericalRange A hz)
      exact hbounded.isCompact_closure
    have hnonempty : (closure (numericalRange A)).Nonempty := by
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      exact ⟨⟪x, A x⟫_ℂ,
        subset_closure ((mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩)⟩
    obtain ⟨hanti, hstageCompact, hstageNonempty, hinter⟩ :=
      compactThickeningApprox_spec (closure (numericalRange A)) hcompact hnonempty
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_support_nested_scalarCompanion_radial_vanishingAtZero
        A Omega (compactThickeningApprox (closure (numericalRange A)))
          hanti hstageCompact hstageNonempty hinter
    · intro n
      rw [hcarrier n]
      unfold compactThickeningApprox convexThickeningApprox
      rw [closure_thickening]
      unfold smoothApproxRadius
      positivity
    · intro n
      rw [hcarrier n]
      apply Metric.self_subset_thickening
      unfold smoothApproxRadius
      positivity
    · exact hsupport
    · intro n
      rw [hcarrier (n + 1), hcarrier n]
      exact closure_convexThickeningApprox_succ_subset
        (closure (numericalRange A)) n
    · exact happrox
