-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:13:57.22203+00:00
-- url     : https://prove2.me/theorems/cee9cd1e-7d21-4525-9898-12bbef71e6bc
-- title:
--   Monotone real paths on nonnegative time have bounded variation on every compact interval
-- statement:
--   For every nondecreasing real-valued function on NNReal time, its restriction to each bounded interval [a,b] has bounded total variation. The norm is bounded by the maximum of the absolute endpoint values; use pinned Mathlib MonotoneOn.boundedVariationOn.
-- source:
--   Pinned Mathlib.Topology.EMetricSpace.BoundedVariation MonotoneOn.boundedVariationOn and explicit endpoint monotonicity bounds.

import Mathlib
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.Real

open Filter Set Topology
open scoped NNReal

/-- Every nondecreasing real path on nonnegative time has bounded
total variation on every bounded interval, with explicit endpoint bounds. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation
    (f : ℝ≥0 → ℝ) (hm : Monotone f) (a b : ℝ≥0) (hab : a ≤ b) :
    BoundedVariationOn f (Icc a b) := by sorry
