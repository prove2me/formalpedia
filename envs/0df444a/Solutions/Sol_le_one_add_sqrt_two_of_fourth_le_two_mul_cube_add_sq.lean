-- Prove2me | solution 1 for le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:46:14.76062+00:00
-- url     : https://prove2.me/submissions/e85f12ef-9dfe-4272-8b35-b32ef00106eb

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia

set_option autoImplicit false
open scoped InnerProductSpace
theorem _root_.solution
    {K : ℝ} (hK : 0 ≤ K) (hfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2) :
    K ≤ 1 + Real.sqrt 2 := by
  by_cases hKzero : K = 0
  · rw [hKzero]
    exact add_nonneg zero_le_one (Real.sqrt_nonneg 2)
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
  have hKsqpos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hquad : K ^ 2 ≤ 2 * K + 1 := by
    nlinarith only [hfour, hKsqpos]
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  by_contra hbound
  have hlt : 1 + Real.sqrt 2 < K := lt_of_not_ge hbound
  nlinarith only [hquad, hsqrt_sq, hsqrt_nonneg, hlt]
