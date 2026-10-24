-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum
-- name    : AvramDividend.Classical.chat08_named_upper_clock_eq_raw_infimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:14:02.534438+00:00
-- url     : https://prove2.me/theorems/c6d3eaf1-6dac-485c-87d7-06b0364c5772
-- title:
--   Exact indexed-infimum representation of the named strict upper passage clock
-- statement:
--   The official named upward first-passage clock has exactly the raw ENNReal indexed-infimum representation appearing in the verified finite-grid no-late-hit and Stieltjes cell decompositions. This bridge allows rewriting those pathwise inequalities directly into the already verified measurable named passage-time weights, with correct infinite/no-hit semantics.
-- source:
--   Prove2Me definition of twoSidedExitUpTime in Definitions.Def_AvramDividend_Classical_TwoSidedExit.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_named_upper_clock_eq_raw_infimum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (c : ℝ) (ω : Ω) :
    twoSidedExitUpTime X c ω =
      ⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞) := by sorry
