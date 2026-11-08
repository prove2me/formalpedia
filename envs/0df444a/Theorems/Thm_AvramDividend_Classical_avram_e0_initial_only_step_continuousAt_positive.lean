-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_step_continuousAt_positive
-- name    : AvramDividend.Classical.avram_e0_initial_only_step_continuousAt_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:01:55.234205+00:00
-- url     : https://prove2.me/theorems/c5d96359-b216-4443-9c83-e35a68383fcd
-- title:
--   An initial-only dividend step is continuous at every positive clock
-- statement:
--   For an arbitrary random initial amount, the dividend path which is zero at clock zero and thereafter constant is continuous at every strictly positive clock. This establishes the positive-clock branch of source-exact left continuity, independently of the zero-clock singleton branch.
-- source:
--   Original Avram IsDividendStrategy and pinned Mathlib continuity of eventual equal functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_only_step_continuousAt_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ≥0 => if s = 0 then (0 : ℝ) else K ω) t := by sorry
