-- Prove2me | solution 1 for exists_norm_bound_crouzeixPolynomialAuxiliaryOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:37.46303+00:00
-- url     : https://prove2.me/submissions/9882c0f3-f6b5-4eed-a128-247c543f06df

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_exists_bound_crouzeixPolynomialAuxiliaryIntegrand
import Theorems.Thm_norm_crouzeixPolynomialAuxiliaryOperator_le

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ∃ C : ℝ, ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  obtain ⟨C, hC⟩ := exists_bound_crouzeixPolynomialAuxiliaryIntegrand A Omega p hOmega
  exact ⟨C, norm_crouzeixPolynomialAuxiliaryOperator_le A Omega p hC⟩
