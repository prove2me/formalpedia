-- Prove2me | Theorems.Thm_ClassicalComplexWPT_hasFPowerSeriesOnBall_sumTsum
-- name    : ClassicalComplexWPT.hasFPowerSeriesOnBall_sumTsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:01.997329+00:00
-- url     : https://prove2.me/theorems/f68e1bc8-961c-580c-a888-c6480e370799
-- title:
--   Classical Complex WPT: has FPower Series On Ball sum Tsum
-- statement:
--   A common-radius normal-convergence criterion for summing an arbitrary family of
--   formal multilinear series.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalSum.lean#L44-L95
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalSum.lean#L44-L95

import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Definitions.Def_ClassicalComplexWPT_NormalSum
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
open ClassicalComplexWPT
variable {𝕜 E F I : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem ClassicalComplexWPT.hasFPowerSeriesOnBall_sumTsum
    (p : I → FormalMultilinearSeries 𝕜 E F) (r : ℝ≥0) (hr : 0 < r)
    (hcoeff : ∀ n, Summable (fun i ↦ ‖p i n‖))
    (hmajor : Summable (fun n ↦ (∑' i, ‖p i n‖) * (r : ℝ) ^ n)) :
    HasFPowerSeriesOnBall (sumTsum p) (seriesTsum p) 0 r := by sorry
