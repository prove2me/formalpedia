-- Prove2me | solution 1 for norm_triple_le_of_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:13.572792+00:00
-- url     : https://prove2.me/submissions/732217f7-bde6-4227-9e82-cc6a2274595c

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_polynomial_calculus_triple_le
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p : Polynomial ℂ) (hp : polynomialSupNorm p S ≤ m)
    (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ)
    (hq : ∀ n, polynomialSupNorm (q n) S ≤ m)
    (hlim : Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
      (nhds G)) :
    ‖Polynomial.aeval A p * G * Polynomial.aeval A p‖ ≤ K * m ^ 3 := by
  have htripleLim : Filter.Tendsto
      (fun n ↦ Polynomial.aeval A p * Polynomial.aeval A (q n) *
        Polynomial.aeval A p) Filter.atTop
      (nhds (Polynomial.aeval A p * G * Polynomial.aeval A p)) :=
    (tendsto_const_nhds.mul hlim).mul tendsto_const_nhds
  apply le_of_tendsto htripleLim.norm
  filter_upwards with n
  refine (norm_polynomial_calculus_triple_le A hK hS hcalc p (q n)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hK
  have hp0 := polynomialSupNorm_nonneg p S
  have hq0 := polynomialSupNorm_nonneg (q n) S
  have hqn := hq n
  calc
    polynomialSupNorm p S ^ 2 * polynomialSupNorm (q n) S ≤
        m ^ 2 * polynomialSupNorm (q n) S := by gcongr
    _ ≤ m ^ 2 * m := by gcongr
    _ = m ^ 3 := by ring
