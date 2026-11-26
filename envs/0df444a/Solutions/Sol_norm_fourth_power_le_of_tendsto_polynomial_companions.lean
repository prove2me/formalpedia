-- Prove2me | solution 1 for norm_fourth_power_le_of_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:02.940009+00:00
-- url     : https://prove2.me/submissions/a17b77f7-fe59-4dfa-9905-4a0aee14413a

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_fourth_power_le_of_companion_calculus_bounds
import Theorems.Thm_norm_triple_le_of_tendsto_polynomial_companions

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
    (p : Polynomial ℂ) (hp : polynomialSupNorm p S ≤ m)
    (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ)
    (hq : ∀ n, polynomialSupNorm (q n) S ≤ m)
    (hlim : Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
      (nhds G))
    (hsymm : ‖Polynomial.aeval A p + star G‖ ≤ 2 * m) :
    ‖Polynomial.aeval A p‖ ^ 4 ≤
      (2 * K ^ 3 + K ^ 2) * m ^ 4 := by
  apply norm_fourth_power_le_of_companion_calculus_bounds
    (Polynomial.aeval A p) G hK hm hsymm
  · exact (hcalc p).trans (mul_le_mul_of_nonneg_left hp hK)
  · exact norm_triple_le_of_tendsto_polynomial_companions
      A hK hS hcalc p hp G q hq hlim
