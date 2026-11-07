-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_ray_compact_glue
-- name    : AvramDividend.Classical.avram_p4_f4_turn17_ray_compact_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:21:11.828427+00:00
-- url     : https://prove2.me/theorems/af7aa1e6-8f7d-4bc4-8c00-572ce0fc67e4
-- title:
--   Join a ray exponential bound to a compact upper bound
-- statement:
--   Elementary partition of the real line and monotonic exponential scale for nonnegative input.
-- source:
--   Source-exact mathematical reduction of f8c60858; independent positive ray, initial compact interval and global glue.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn17_ray_compact_glue
    (r : ℝ) (hr : 0 ≤ r) (w : ℝ → ℝ)
    (hw_neg : ∀ y < 0, w y = 0)
    (K M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hRay : ∀ y : ℝ, 1 ≤ y → w y ≤ K * Real.exp (r * y))
    (hCompact : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ,
      w y ≤ L * Real.exp (r * y) := by sorry
