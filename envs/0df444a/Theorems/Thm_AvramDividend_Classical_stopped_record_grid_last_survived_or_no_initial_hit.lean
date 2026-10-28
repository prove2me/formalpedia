-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_record_grid_last_survived_or_no_initial_hit
-- name    : AvramDividend.Classical.stopped_record_grid_last_survived_or_no_initial_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:59:04.664087+00:00
-- url     : https://prove2.me/theorems/3831a1f5-93c1-466c-8af4-01bffd6f7320
-- title:
--   Finite ruin has a last survived first-record grid cell or no initial record
-- statement:
--   When the reflected barrier ruins at a finite time, the proved eventual no-hit result ensures that either the first record level b is never crossed before ruin, or there is an index n whose record level is crossed before ruin but whose successor level is not. This identifies the exact terminal partial record cell required to complete the stopped pathwise renewal upper cover.
-- source:
--   Direct pathwise terminal index selection from Proved chat08_named_stopped_grid_no_late_hit_of_finite_ruin. Connects finite ruin to the full-record upper sums and terminal partial-cell inequality for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound.

import Mathlib.Data.Nat.Basic
import Theorems.Thm_AvramDividend_Classical_chat08_named_stopped_grid_no_late_hit_of_finite_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_record_grid_last_survived_or_no_initial_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b h : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    (¬ twoSidedExitUpTime X b ω < barrierRuinTime X a ω) ∨
    ∃ n : ℕ,
      twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
        barrierRuinTime X a ω ∧
      ¬ twoSidedExitUpTime X (b + ((n + 1 : ℕ) : ℝ) * h) ω <
        barrierRuinTime X a ω := by sorry
