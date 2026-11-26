-- Prove2me | solution 1 for crouzeix_palencia_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:12.621994+00:00
-- url     : https://prove2.me/submissions/a3f492fb-115b-417c-b69b-240bba43a242

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_of_isStarNormal
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_spectrum_subset_closure_numericalRange

section
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private theorem isCompact_closure_numericalRange_palencia (A : E →L[ℂ] E) :
    IsCompact (closure (numericalRange A)) := by
  have hbounded : Bornology.IsBounded (numericalRange A) :=
    Metric.isBounded_closedBall.subset (fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz)
  exact hbounded.isCompact_closure
variable [CompleteSpace E]
end

set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) [IsStarNormal A] :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    have hm : 0 ≤ polynomialSupNorm p (closure (numericalRange A)) :=
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
    calc
      ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (closure (numericalRange A)) :=
        norm_aeval_le_polynomialSupNorm_of_isStarNormal A
          (isCompact_closure_numericalRange_palencia A)
          (spectrum_subset_closure_numericalRange A) p
      _ = 1 * polynomialSupNorm p (closure (numericalRange A)) := by rw [one_mul]
      _ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (closure (numericalRange A)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg 2)) hm
