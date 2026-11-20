-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_abovecap_corrected_parenthesised_grid_defect_sum
-- name    : AvramDividend.Classical.avram_f6_abovecap_corrected_parenthesised_grid_defect_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:03:48.186171+00:00
-- url     : https://prove2.me/theorems/0523a855-34f4-4b44-b080-1611b2244f3b
-- title:
--   Correct above-cap grid defect sum has parenthesised per-cell subtraction and equals two
-- statement:
--   For all m>0, the true sum of each original above-cap cell's caplinear-versus-w defect equals two: the subtraction must be parenthesised inside the finite summand, unlike false theorem d19b426d where it scopes outside. Provides a mathematically valid replacement of that theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_f6_abovecap_corrected_parenthesised_grid_defect_sum
    (m : ℕ) (hm : 0 < m) :
    let w : ℝ → ℝ := fun y =>
      if y < 0 then 0 else if y ≤ 1 then y else 2 - y
    let V : ℝ → ℝ := fun y =>
      if y ≤ 1 then w y else w 1 + (y - 1)
    (∑ _i ∈ Finset.range m,
      (V (1 + 1 / (m : ℝ)) - w (1 + 1 / (m : ℝ)))) = 2 := by sorry
