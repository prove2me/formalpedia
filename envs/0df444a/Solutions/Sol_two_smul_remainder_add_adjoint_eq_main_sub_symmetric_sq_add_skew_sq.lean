-- Prove2me | solution 1 for two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:39.600863+00:00
-- url     : https://prove2.me/submissions/679a67d9-409c-4168-9f11-43c737e86f60

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (F G H Q : E →L[ℂ] E) (hdecomp : F * G = H - Q) :
    (2 : ℂ) • (Q + star Q) =
      (2 : ℂ) • (H + star H) -
        (F + star G) * (star F + G) +
        (F - star G) * (star F - G) := by
  have hH : H = F * G + Q := by
    rw [hdecomp]
    module
  rw [hH]
  simp only [two_smul, star_add, star_mul]
  noncomm_ring
