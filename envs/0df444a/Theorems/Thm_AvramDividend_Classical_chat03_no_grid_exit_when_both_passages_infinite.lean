-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
-- name    : AvramDividend.Classical.chat03_no_grid_exit_when_both_passages_infinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:14:56.359413+00:00
-- url     : https://prove2.me/theorems/9ae1ae51-8110-4836-bb1b-007f9fa5b780
-- title:
--   No strict grid or continuous two-sided exit when both named passage clocks are infinite
-- statement:
--   For the exact official strict upper and lower first-passage times in ℝ≥0∞, if both equal infinity then the Lévy sample path has no strict two-sided exit at any nonnegative real time. Consequently no uniform grid of any positive or nonnegative mesh size ever samples a strict exit at any index. This covers the true infinity/no-crossing branch separately from finite IsGLB first-grid approximation and preserves strict boundary semantics.
-- source:
--   The independently Proved generic extended-infimum infinity/no-witness theorem on the exact named first-passage clock predicates, pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_no_grid_exit_when_both_passages_infinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ)
    (hUp : twoSidedExitUpTime X upper ω = ∞)
    (hDown : twoSidedExitDownTime X lower ω = ∞) :
    (∀ t : ℝ≥0,
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)) ∧
    (∀ h : ℝ≥0, ∀ k : ℕ,
      ¬ (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω)) := by sorry
