-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a67_original_strict_positive_uniform_clock_tendsto
-- name    : AvramDividend.Classical.avram_bva_a67_original_strict_positive_uniform_clock_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:08:35.139573+00:00
-- url     : https://prove2.me/theorems/447fabd1-322c-43fb-af23-0444c2c9cfac
-- title:
--   Cofinal strict positive deterministic prehorizon clocks tend to T from the left
-- statement:
--   For each T>0, the nonnegative deterministic clocks r_n = max(T−T/(n+2),0) converge strictly from the left to the NNReal horizon T. Used to apply the existing Proved original killed prepayment terminal left-grid lower bound, thereby preserving the actual prepayment convention in the infinite-activity BV cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a67_original_strict_positive_uniform_clock_tendsto
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => Real.toNNReal (T - T / ((n : ℝ) + 2)))
      atTop (𝓝[<] (⟨T, le_of_lt hT⟩ : ℝ≥0)) := by sorry
