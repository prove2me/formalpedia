-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_weight_nat_caps_monotone
-- name    : AvramDividend.Classical.killed_weight_nat_caps_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:18:05.247816+00:00
-- url     : https://prove2.me/theorems/6ad8d019-10fa-43a6-bf14-23865b82c906
-- title:
--   Killed extended-time reward truncated at natural horizons increases with the horizon
-- statement:
--   For a nonnegative extended-valued killed reward, its finite-horizon truncation is increasing in the horizon. This supplies the monotonicity hypothesis for monotone convergence of localised killed-record rewards.
-- source:
--   Monotonicity of natural-number embeddings into ENNReal and bottom inequality

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_weight_nat_caps_monotone
    {Ω : Type*} (T : Ω → ℝ≥0∞) (weight : Ω → ℝ≥0∞) :
    Monotone (fun n : ℕ => fun ω : Ω =>
      if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) := by sorry
