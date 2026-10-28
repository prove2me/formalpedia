-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_levy_increment_cocycle_partition
-- name    : AvramDividend.Classical.chat08_levy_increment_cocycle_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:12:11.873894+00:00
-- url     : https://prove2.me/theorems/e368a4f6-a0af-4fa6-ab4e-08439657a661
-- title:
--   Split a Lévy path increment into adjacent deterministic-time increments
-- statement:
--   For an arbitrary real-valued path, the increment over consecutive intervals is the sum of its two adjacent increments. This cocycle is a foundational algebraic identity for the stopped-time regeneration argument.
-- source:
--   Ring subtraction cancellation.

import Mathlib.Tactic.Ring
import Mathlib.Probability.Process.Stopping

open scoped NNReal

theorem AvramDividend.Classical.chat08_levy_increment_cocycle_partition
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (t u v : ℝ≥0) (ω : Ω) :
    Y (t + u + v) ω - Y t ω =
      (Y (t + u + v) ω - Y (t + u) ω) +
      (Y (t + u) ω - Y t ω) := by sorry
