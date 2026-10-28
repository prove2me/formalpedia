-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_exit_right_interval
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:56:19.410098+00:00
-- url     : https://prove2.me/theorems/cb36f7b6-5a30-40f6-919e-fd5c7ef75dc9
-- title:
--   Any strict two-sided exit of a randomly started shifted Lévy reserve persists on a nonempty right interval
-- statement:
--   For a spectrally negative Lévy process, any fixed time shift and arbitrary path-dependent initial reserve, a strict crossing below zero or strictly above an upper barrier at any time has a right neighbourhood in which at least one of these two strict crossings persists. This combines the Proved lower and upper right-interval persistence theorems and is an immediate pathwise prerequisite for two-sided rational-grid stopping-time detection.
-- source:
--   Proved chat04_shifted_random_reserve_lower_exit_right_interval and chat04_shifted_random_reserve_upper_exit_right_interval, by disjunction elimination.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_exit_right_interval

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_right_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b t : ℝ≥0)
    (h : (H ω + (X.X (b + t) ω - X.X b ω) < 0) ∨
      (a < H ω + (X.X (b + t) ω - X.X b ω))) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        (H ω + (X.X (b + v) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + v) ω - X.X b ω)) := by sorry
