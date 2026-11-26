-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_continuous_scalar_companion_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:14.155337+00:00
-- url     : https://prove2.me/submissions/cef05575-b57f-4416-9f99-98d65b9ffd2e

import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation
import Theorems.Thm_convexThickeningApprox_spec
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_frontier_convexThickeningApprox_subset_compactThickeningApprox
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
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
      ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
        ContinuousOn g
          ((Omega n).boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
        (∀ z ∈ compactThickeningApprox (closure (numericalRange A)) n,
          ‖g z‖ ≤ polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        (∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
        crouzeixAuxiliaryOperator A (Omega n) g =
          crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : Set ℂ := closure (numericalRange A)
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_closure_numericalRange_smoothApproximation A
  have hKconvex : Convex ℝ K := by
    simpa only [K] using (convex_numericalRange A).closure
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_contractive_scalar_companion_approximation
      A Omega hcarrier hCauchyP hsupport
  intro p n
  obtain ⟨g, r, hgcont, hgbound, happrox, hPlemelj⟩ := hcompanion p n
  refine ⟨g, r, hgbound, happrox, ?_⟩
  have hOmega : closure (numericalRange A) ⊆ (Omega n).carrier := by
    rw [hcarrier n]
    exact (convexThickeningApprox_spec K hKcompact hKconvex).1 n |>.1
  have hboundaryApprox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval ((Omega n).boundaryParam t) (r j) -
        g ((Omega n).boundaryParam t)‖ ≤ 1 / ((j : ℝ) + 1) := by
    intro j t ht
    apply happrox j ((Omega n).boundaryParam t)
    have hfrontier : (Omega n).boundaryParam t ∈
        frontier (Omega n).carrier := by
      rw [← (Omega n).boundaryParam_range]
      exact mem_range_self t
    rw [hcarrier n] at hfrontier
    exact frontier_convexThickeningApprox_subset_compactThickeningApprox
      (closure (numericalRange A)) n hfrontier
  have hlim :=
    tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
      A (Omega n) g r hOmega hgcont (fun j ↦ hCauchyP (r j) n)
        hboundaryApprox
  simpa only [hPlemelj] using hlim
