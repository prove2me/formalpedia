-- Prove2me | solution 1 for exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:15.376016+00:00
-- url     : https://prove2.me/submissions/35cddc57-0880-4d61-ae0b-4d573dd4af45

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_exists_smoothJordanDomain_for_numericalRange
import Theorems.Thm_exists_norm_bound_crouzeixPolynomialAuxiliaryOperator

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    ∃ (Omega : SmoothJordanDomain) (C : ℝ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
      ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  obtain ⟨Omega, hOmega⟩ := exists_smoothJordanDomain_for_numericalRange A
  obtain ⟨C, hC⟩ := exists_norm_bound_crouzeixPolynomialAuxiliaryOperator A Omega p hOmega
  exact ⟨Omega, C, hOmega, hC⟩
