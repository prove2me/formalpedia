-- Prove2me | solution 1 for exists_bound_crouzeixPolynomialAuxiliaryIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:58.272503+00:00
-- url     : https://prove2.me/submissions/7c7b338e-95ff-490b-b55a-ce59a44fbd1d

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))‖ ≤ C := by
  have hgamma : ContinuousOn Omega.boundaryParam (Icc (0 : ℝ) (2 * Real.pi)) :=
    Omega.boundaryParam_contDiff.continuous.continuousOn
  have hresolvent : ContinuousOn (resolvent A)
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
    rintro z ⟨t, ht, rfl⟩
    exact (spectrum.hasDerivAt_resolvent_const_left
      (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt
  have hkernel : ContinuousOn
      (fun t => star (Polynomial.eval (Omega.boundaryParam t) p) •
        resolvent A (Omega.boundaryParam t)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    (p.continuous.star.continuousOn.smul hresolvent).comp hgamma (mapsTo_image _ _)
  have hintegrand : ContinuousOn
      (fun t => deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))) (Icc (0 : ℝ) (2 * Real.pi)) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn.smul hkernel
  have himage : IsCompact ((fun t => deriv Omega.boundaryParam t •
      (star (Polynomial.eval (Omega.boundaryParam t) p) •
        resolvent A (Omega.boundaryParam t))) '' Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image_of_continuousOn hintegrand
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : E →L[ℂ] E)).mp himage.isBounded
  refine ⟨C, fun t ht => ?_⟩
  have hmem := hC ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  exact hmem
