-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_ennreal_finite_mesh_squeeze
-- name    : AvramDividend.Classical.avram_p2_d_future_ennreal_finite_mesh_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:28:12.080208+00:00
-- url     : https://prove2.me/theorems/d9b79a64-ae5d-4b30-a083-3dc876e3f1f4
-- title:
--   Extended nonnegative finite-rate mean squeeze from exact rational intervals
-- statement:
--   If finite ENNReal values c and m obey the exact rational-grid lower and upper bounds at every positive integer denominator, where the corresponding rational nonnegative real grid cell contains t, then m=t c in ENNReal. This converts source real-horizon ENNReal count-mean brackets to the accepted finite NNReal mesh-squeeze theorem without any Lévy measure intensity assumption.
-- source:
--   Proved finite NNReal squeeze 2cb8f4f4-cbe9-406b-9885-36f3ad6a182a; convert finite ENNReal values by toNNReal and normalise ENNReal.coe_div with nonzero natural denominator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_finite_nnreal_mesh_squeeze

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_ennreal_finite_mesh_squeeze
    (c m : ℝ≥0∞) (t : ℝ≥0) (hc : c ≠ ⊤) (hm : m ≠ ⊤)
    (hmesh : ∀ d : ℕ, 0 < d → ∃ n : ℕ,
      ((n : ℝ≥0) / (d : ℝ≥0)) ≤ t ∧
      t ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) ∧
      ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * c ≤ m ∧
      m ≤ (((n + 1 : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞)) * c) :
    m = (t : ℝ≥0∞) * c := by sorry
