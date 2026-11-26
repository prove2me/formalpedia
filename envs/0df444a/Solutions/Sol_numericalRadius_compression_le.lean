-- Prove2me | solution 1 for numericalRadius_compression_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:44:47.279536+00:00
-- url     : https://prove2.me/submissions/5111e92f-d62f-4b5c-8c6b-5b682cb236c9

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_Compression
import Theorems.Thm_numericalRange_compression_subset
import Theorems.Thm_norm_le_numericalRadius
import Theorems.Thm_numericalRadius_nonneg


set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem _root_.solution
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) (hV : Isometry V) :
    numericalRadius ((V† ∘L A) ∘L V) ≤ numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_) (numericalRadius_nonneg A)
  refine Real.iSup_le (fun hz => ?_) (numericalRadius_nonneg A)
  exact norm_le_numericalRadius A (numericalRange_compression_subset A V hV hz)
