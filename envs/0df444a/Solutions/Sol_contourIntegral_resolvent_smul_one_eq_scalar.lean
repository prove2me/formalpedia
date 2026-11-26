-- Prove2me | solution 1 for contourIntegral_resolvent_smul_one_eq_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:08.490207+00:00
-- url     : https://prove2.me/submissions/c8c1076b-632e-459c-ad2c-321f0d80b966

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_resolvent_smul_one_eq_inv_smul_one

set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (Omega : SmoothJordanDomain) (c : ℂ)
    (hc : c ∈ Omega.carrier) :
    contourIntegral (resolvent (c • (1 : E →L[ℂ] E)))
        Omega.boundaryParam =
      contourIntegral (fun z : ℂ => (z - c)⁻¹) Omega.boundaryParam •
        (1 : E →L[ℂ] E) := by
  have hne : ∀ t : ℝ, Omega.boundaryParam t ≠ c := by
    intro t heq
    have hfrontier : c ∈ frontier Omega.carrier := by
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : c ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hc, hfrontier⟩
    exact hempty
  unfold contourIntegral
  have hfun :
      (fun t : ℝ => deriv Omega.boundaryParam t •
        resolvent (c • (1 : E →L[ℂ] E)) (Omega.boundaryParam t)) =
      fun t : ℝ =>
        (deriv Omega.boundaryParam t *
          (Omega.boundaryParam t - c)⁻¹) • (1 : E →L[ℂ] E) := by
    funext t
    rw [resolvent_smul_one_eq_inv_smul_one c
      (Omega.boundaryParam t) (hne t), smul_smul]
  rw [hfun, intervalIntegral.integral_smul_const]
  rfl
