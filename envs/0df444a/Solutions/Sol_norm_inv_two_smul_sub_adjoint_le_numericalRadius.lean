-- Prove2me | solution 1 for norm_inv_two_smul_sub_adjoint_le_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:46.780944+00:00
-- url     : https://prove2.me/submissions/973dc7a0-17cf-4375-9c70-0378626ad991

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
import Theorems.Thm_norm_sub_adjoint_le_two_mul_numericalRadius

set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    ‖(2 : ℂ)⁻¹ • (A - A†)‖ ≤ numericalRadius A := by
  have hc : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℂ)⁻¹ • (A - A†)‖ = (2 : ℝ)⁻¹ * ‖A - A†‖ := by
      rw [norm_smul, hc]
    _ ≤ (2 : ℝ)⁻¹ * (2 * numericalRadius A) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_adjoint_le_two_mul_numericalRadius A) (by positivity)
    _ = numericalRadius A := by ring
