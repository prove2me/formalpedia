-- Prove2me | solution 1 for crouzeixAuxiliaryIntegrand_contourIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:50.137812+00:00
-- url     : https://prove2.me/submissions/12c0b16e-8576-43d0-8c20-421db38019a1

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet
import Theorems.Thm_ContourIntegrable_of_continuousOn


set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E] (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    ContourIntegrable (fun z => h z • resolvent A z) Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · refine hh.smul ?_
    rintro z ⟨t, ht, rfl⟩
    exact (spectrum.hasDerivAt_resolvent_const_left
      (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt
