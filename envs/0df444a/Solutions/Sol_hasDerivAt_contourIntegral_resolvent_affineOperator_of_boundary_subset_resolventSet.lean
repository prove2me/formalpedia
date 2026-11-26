-- Prove2me | solution 1 for hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:07.254715+00:00
-- url     : https://prove2.me/submissions/2aa49dfa-8413-4a92-a77a-a31de28268a0

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_hasDerivAt_contourIntegral_resolvent_affineOperator
import Theorems.Thm_exists_resolvent_affineOperator_neighborhood_bound

set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      (contourIntegral
        (fun z : ℂ =>
          resolvent (B + s • D) z * D * resolvent (B + s • D) z)
        Omega.boundaryParam) s := by
  obtain ⟨epsilon, C, hepsilon, hC, hlocal⟩ :=
    exists_resolvent_affineOperator_neighborhood_bound
      B D Omega s hres
  apply hasDerivAt_contourIntegral_resolvent_affineOperator
    B D Omega s hepsilon hC
  · exact fun w hw t => (hlocal w hw t).1
  · exact fun w hw t => (hlocal w hw t).2
