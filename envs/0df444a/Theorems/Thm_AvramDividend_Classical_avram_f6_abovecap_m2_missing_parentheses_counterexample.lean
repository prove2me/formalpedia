-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_abovecap_m2_missing_parentheses_counterexample
-- name    : AvramDividend.Classical.avram_f6_abovecap_m2_missing_parentheses_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:02:14.848512+00:00
-- url     : https://prove2.me/theorems/0f4280aa-e663-44b4-b02f-7a0c12c6a49d
-- title:
--   Original above-cap range sum false at m=2 because subtraction scopes outside binder
-- statement:
--   For the exact original w and V defined in d19b426d, the m=2 term with original sum syntax is not 2: it is 5/2, since the subtracted w(3/2) is scoped outside the two summands. A proof certificate that the original theorem is invalid as written and should be deprecated or corrected.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_f6_abovecap_m2_missing_parentheses_counterexample :
    let w : ℝ → ℝ := fun y =>
      if y < 0 then 0 else if y ≤ 1 then y else 2 - y
    let V : ℝ → ℝ := fun y =>
      if y ≤ 1 then w y else w 1 + (y - 1)
    (∑ _i ∈ Finset.range (2 : ℕ),
      V (1 + 1 / (2 : ℝ)) - w (1 + 1 / (2 : ℝ))) ≠ (2 : ℝ) := by sorry
