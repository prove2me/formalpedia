-- Prove2me | solution 1 for polynomialSupNorm_C_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:53.368383+00:00
-- url     : https://prove2.me/submissions/92b245cf-1052-4186-a88a-362731744d6b

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_eval_le_polynomialSupNorm
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (a : ℂ) {K : Set ℂ}
    (hK : K.Nonempty) : polynomialSupNorm (Polynomial.C a) K = ‖a‖ := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun z => ?_) (norm_nonneg a)
    exact Real.iSup_le (fun hz => by
      simp only [Polynomial.eval_C]
      exact le_rfl) (norm_nonneg a)
  · obtain ⟨z, hz⟩ := hK
    simpa only [Polynomial.eval_C] using
      (norm_eval_le_polynomialSupNorm (Polynomial.C a)
        ⟨‖a‖, by
          rintro _ ⟨w, hw, rfl⟩
          simp only [Polynomial.eval_C]
          exact le_rfl⟩ hz)
