-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_leftcont
-- name    : AvramDividend.Classical.avram_e0_initial_only_dividend_leftcont
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:55:29.584902+00:00
-- url     : https://prove2.me/theorems/749f8dc1-0ac2-4948-9d72-15dde78cdfa7
-- title:
--   A dividend payment only at the origin is left-continuous at every clock
-- statement:
--   An initial-only dividend step has a zero singleton past at time zero and is constant on a sufficiently small left neighbourhood of every strictly positive time. It therefore satisfies the exact source left-continuity field of IsDividendStrategy.
-- source:
--   Original Avram IsDividendStrategy and pinned Mathlib topology ContinuousWithinAt.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_dividend_leftcont
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (ω : Ω) :
    ∀ t : ℝ≥0, ContinuousWithinAt
      (fun s : ℝ≥0 => if s = 0 then (0 : ℝ) else K ω) (Iic t) t := by sorry
