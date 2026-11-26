-- Prove2me | solution 1 for norm_crouzeixAuxiliaryOperator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:54.472116+00:00
-- url     : https://prove2.me/submissions/51a2c3c2-6d2d-433e-8750-642c8d61a547

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_norm_contourIntegral_le_of_norm_le_const


set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (h (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t))‖ ≤ C) :
    ‖crouzeixAuxiliaryOperator A Omega h‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by
  unfold crouzeixAuxiliaryOperator
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (norm_contourIntegral_le_of_norm_le_const hbound) (norm_nonneg _)
