-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:42:48.825738+00:00
-- url     : https://prove2.me/theorems/5c5897cb-27d0-4352-b06b-d3d64b8202b0
-- title:
--   Uniform-mesh original-jump triangular rate tends to the half-square intensity
-- statement:
--   For the genuine source horizon T and original negative-band intensity a, the exact deterministic m-cell triangular rate expression converges to (T*a)^2/2. The theorem is valid for all real inputs and uses only the pinned Archimedean real sequence and reciprocal limit; it is intended for instantiation with a=(X.ν B).toReal and the separately proved finite-grid real rate identity. It makes no Poisson-process pathwise assumption.
-- source:
--   Pinned tendsto_natCast_atTop_atTop, tendsto_inv_atTop_zero, Filter.eventually_gt_atTop; companion new triangular finite-grid rate equality, P2-E exact physical source grid 77b37394.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
    (T a : ℝ) :
    Tendsto
      (fun m : ℕ =>
        ((m : ℝ) * ((m : ℝ) - 1) / 2) *
          ((T * a) ^ 2 / (m : ℝ) ^ 2))
      atTop (𝓝 ((T * a) ^ 2 / 2)) := by sorry
