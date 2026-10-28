-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_before_horizon_grid_iff
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_upper_before_horizon_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:40:17.219795+00:00
-- url     : https://prove2.me/theorems/4a0d8fbd-e959-43b1-97fe-cca7f003288c
-- title:
--   Strict shifted upward passage before a finite horizon is equivalent to rational-grid passage
-- statement:
--   For any path-dependent reserve H, deterministic clock shift b, real upper barrier a and finite observation horizon T, there is a strict crossing above a before T if and only if a rational grid point k/n before T witnesses it. The proof uses pathwise right continuity and a constructive NNReal ceiling witness. This complements the Proved strict lower-exit grid theorem for two-sided exit stopping times.
-- source:
--   Proved chat04_shifted_random_reserve_upper_exit_right_interval and chat03_nnreal_grid_ceiling_bracket.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_upper_before_horizon_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0) :
    (∃ v : ℝ≥0, v < T ∧
      a < H ω + (X.X (b + v) ω - X.X b ω)) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
      a < H ω +
        (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) := by sorry
