-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
-- name    : AvramDividend.Classical.cstar_toReal_zero_or_minimal_of_deriv_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T15:06:36.029489+00:00
-- url     : https://prove2.me/theorems/a1caec2e-842f-4447-97c9-0f1fb76e0b94
-- title:
--   A positive c-star is a derivative minimiser under continuity
-- statement:
--   For any W with derivative continuous on the positive half-line, the real interpretation of the canonical cstar is zero or is positive and minimises the derivative on the positive half-line. This follows from the proved real-argmin closure lemma and a bridge between the extended nonnegative infimum and the real set infimum. No assumption of cstar finiteness is required because infinity.toReal is zero.
-- source:
--   Avram Classical campaign, proposed to strengthen milestone 4 independent of milestone 2; proof source hash a0e9be0fb076a3598cb74c264559557628faaa0e7dd48cba3b490de826512c0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal
open Set
open scoped ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.cstar_toReal_zero_or_minimal_of_deriv_continuous (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0)) :
    (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x →
          deriv W (cstar W).toReal ≤ deriv W x) := by
  sorry
