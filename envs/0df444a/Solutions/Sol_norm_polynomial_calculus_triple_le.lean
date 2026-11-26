-- Prove2me | solution 1 for norm_polynomial_calculus_triple_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:23.626009+00:00
-- url     : https://prove2.me/submissions/37b41afb-bf9a-4426-9708-cb7a757fe459

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_polynomialSupNorm_mul_mul_le_of_isCompact

set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p q : Polynomial ℂ) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q * Polynomial.aeval A p‖ ≤
      K * (polynomialSupNorm p S ^ 2 * polynomialSupNorm q S) := by
  calc
    ‖Polynomial.aeval A p * Polynomial.aeval A q * Polynomial.aeval A p‖ =
        ‖Polynomial.aeval A (p * q * p)‖ := by
      rw [Polynomial.aeval_mul, Polynomial.aeval_mul]
    _ ≤ K * polynomialSupNorm (p * q * p) S := hcalc _
    _ ≤ K * (polynomialSupNorm p S ^ 2 * polynomialSupNorm q S) :=
      mul_le_mul_of_nonneg_left
        (polynomialSupNorm_mul_mul_le_of_isCompact hS p q) hK
