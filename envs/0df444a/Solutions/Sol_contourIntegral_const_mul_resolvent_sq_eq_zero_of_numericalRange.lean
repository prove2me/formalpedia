-- Prove2me | solution 1 for contourIntegral_const_mul_resolvent_sq_eq_zero_of_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:00.341824+00:00
-- url     : https://prove2.me/submissions/32383383-a158-43ed-8db7-7ddb47a5974f

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_contourIntegral_const_mul_resolvent_sq_eq_zero
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange B) ⊆ Omega.carrier) :
    contourIntegral (fun z : ℂ => D * resolvent B z ^ 2)
      Omega.boundaryParam = 0 := by
  apply contourIntegral_const_mul_resolvent_sq_eq_zero
  intro t
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  intro hspectrum
  have hcarrier : Omega.boundaryParam t ∈ Omega.carrier :=
    hOmega (spectrum_subset_closure_numericalRange B hspectrum)
  have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hcarrier, hfrontier⟩
  exact hempty
