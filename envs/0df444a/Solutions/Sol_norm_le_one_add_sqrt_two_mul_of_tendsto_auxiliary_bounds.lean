-- Prove2me | solution 1 for norm_le_one_add_sqrt_two_mul_of_tendsto_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:24.511937+00:00
-- url     : https://prove2.me/submissions/0b19e260-0700-4adc-9c0c-58d5929af811

import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Theorems.Thm_norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Filter
open scoped InnerProductSpace
theorem _root_.solution
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F : B) {m : ℝ} (M : ℕ → ℝ) (hM : Tendsto M atTop (nhds m))
    (haux : ∀ n : ℕ, ∃ G : B,
      ‖F + star G‖ ≤ 2 * M n ∧ ‖F * G‖ ≤ (M n) ^ 2) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by
  apply norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds F
  intro ε hε
  have heventually : ∀ᶠ n in atTop, M n < m + ε :=
    (tendsto_order.mp hM).2 (m + ε) (lt_add_of_pos_right m hε)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp heventually
  obtain ⟨G, hsymm, hprod⟩ := haux n
  have hMnlt : M n < m + ε := hn n le_rfl
  have hMn : 0 ≤ M n := by
    linarith only [norm_nonneg (F + star G), hsymm]
  have hmε : 0 ≤ m + ε := hMn.trans hMnlt.le
  refine ⟨G, hsymm.trans ?_, hprod.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left hMnlt.le (by norm_num)
  · simp only [pow_two]
    exact mul_le_mul hMnlt.le hMnlt.le hMn hmε
