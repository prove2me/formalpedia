-- Prove2me | solution 1 for norm_fourth_power_le_of_polynomial_companion_calculus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:14.877284+00:00
-- url     : https://prove2.me/submissions/376e8c9f-86f5-40a5-afdf-df19333b8596

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_fourth_power_le_of_companion_calculus_bounds
import Theorems.Thm_norm_polynomial_calculus_triple_le
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p q : Polynomial ℂ)
    (hp : polynomialSupNorm p S ≤ m)
    (hq : polynomialSupNorm q S ≤ m)
    (hsymm : ‖Polynomial.aeval A p + star (Polynomial.aeval A q)‖ ≤ 2 * m) :
    ‖Polynomial.aeval A p‖ ^ 4 ≤
      (2 * K ^ 3 + K ^ 2) * m ^ 4 := by
  apply norm_fourth_power_le_of_companion_calculus_bounds
    (Polynomial.aeval A p) (Polynomial.aeval A q) hK hm hsymm
  · exact (hcalc p).trans (mul_le_mul_of_nonneg_left hp hK)
  · refine (norm_polynomial_calculus_triple_le A hK hS hcalc p q).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK
    have hp0 := polynomialSupNorm_nonneg p S
    have hq0 := polynomialSupNorm_nonneg q S
    calc
      polynomialSupNorm p S ^ 2 * polynomialSupNorm q S ≤
          m ^ 2 * polynomialSupNorm q S := by gcongr
      _ ≤ m ^ 2 * m := by gcongr
      _ = m ^ 3 := by ring
