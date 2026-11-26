-- Prove2me | solution 1 for polynomialSupNorm_mul_mul_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:44.834271+00:00
-- url     : https://prove2.me/submissions/f2a0881b-a615-435e-a982-ed38bed968e7

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_polynomialSupNorm_mul_le_of_isCompact
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open scoped InnerProductSpace
theorem _root_.solution
    {S : Set ℂ} (hS : IsCompact S) (p q : Polynomial ℂ) :
    polynomialSupNorm (p * q * p) S ≤
      polynomialSupNorm p S ^ 2 * polynomialSupNorm q S := by
  calc
    polynomialSupNorm (p * q * p) S ≤
        polynomialSupNorm (p * q) S * polynomialSupNorm p S :=
      polynomialSupNorm_mul_le_of_isCompact hS (p * q) p
    _ ≤ (polynomialSupNorm p S * polynomialSupNorm q S) *
        polynomialSupNorm p S :=
      mul_le_mul_of_nonneg_right
        (polynomialSupNorm_mul_le_of_isCompact hS p q)
        (polynomialSupNorm_nonneg p S)
    _ = polynomialSupNorm p S ^ 2 * polynomialSupNorm q S := by ring
