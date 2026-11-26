-- Prove2me | solution 1 for norm_crouzeixPolynomialAuxiliaryOperator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:48.469528+00:00
-- url     : https://prove2.me/submissions/29df4b3c-c127-4702-9425-bfd615d3f408

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_norm_crouzeixAuxiliaryOperator_le

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))‖ ≤ C) :
    ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  unfold crouzeixPolynomialAuxiliaryOperator
  exact norm_crouzeixAuxiliaryOperator_le A Omega
    (fun z => star (Polynomial.eval z p)) hbound
