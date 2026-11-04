-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_finite_nnreal_mesh_squeeze
-- name    : AvramDividend.Classical.avram_p2_d_future_finite_nnreal_mesh_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:02:43.509254+00:00
-- url     : https://prove2.me/theorems/2cb8f4f4-cbe9-406b-9885-36f3ad6a182a
-- title:
--   A finite nonnegative rate is uniquely determined at each real horizon by arbitrarily fine rational-grid mean sandwiches
-- statement:
--   If finite nonnegative marked-count mean m is squeezed between the same unit-time slope c times the two endpoints of a rational grid cell containing t, for every positive integer grid denominator, then m equals t times c. No Lévy ν identification, Poisson model, or process change is assumed.
-- source:
--   Elementary NNReal/ENNReal order-squeeze from concrete mesh bounds, using the already Proved P2-D Archimedean c/d<ε helper 73ee1057. Intended for the original source real-time count mean after finite conversion via ENNReal.toNNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_finite_nnreal_mesh_squeeze
    (c t m : ℝ≥0)
    (hmesh : ∀ d : ℕ, 0 < d → ∃ n : ℕ,
      ((n : ℝ≥0) / (d : ℝ≥0)) ≤ t ∧
      t ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) ∧
      ((n : ℝ≥0) / (d : ℝ≥0)) * c ≤ m ∧
      m ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) * c) :
    m = t * c := by sorry
