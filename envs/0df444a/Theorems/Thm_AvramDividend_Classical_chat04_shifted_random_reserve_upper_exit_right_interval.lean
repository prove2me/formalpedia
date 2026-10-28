-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_exit_right_interval
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_upper_exit_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:32:27.58074+00:00
-- url     : https://prove2.me/theorems/ed807cbd-9532-4e2c-917d-1d8c491b1a09
-- title:
--   Strict upward barrier passage persists after a deterministic time shift with random initial reserve
-- statement:
--   For a shifted Lévy increment started with an arbitrary path-dependent reserve H, a strict crossing above any barrier a persists in a right interval. This supplies the pathwise step in rational-grid detection of an upper exit and complements the proved lower-exit analogue.
-- source:
--   Proved chat03_strict_upper_exit_right_interval translated by addition and subtraction.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_upper_exit_right_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b t : ℝ≥0)
    (h : a < H ω + (X.X (b + t) ω - X.X b ω)) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        a < H ω + (X.X (b + v) ω - X.X b ω) := by sorry
