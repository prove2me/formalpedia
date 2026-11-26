-- Prove2me | solution 1 for polynomialSupNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:42:40.061008+00:00
-- url     : https://prove2.me/submissions/912a56d2-95a2-42a1-94e8-7c41d5c93cc6

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution (a : ℂ) (p : Polynomial ℂ) (X : Set ℂ) :
    polynomialSupNorm (a • p) X = ‖a‖ * polynomialSupNorm p X := by
  simp only [polynomialSupNorm, Polynomial.eval_smul, norm_smul]
  rw [Real.mul_iSup_of_nonneg (norm_nonneg a)]
  congr with z
  rw [Real.mul_iSup_of_nonneg (norm_nonneg a)]
