-- Prove2me | Theorems.Thm_ClassicalComplexWPT_summable_nnnorm_changeOriginSeries_mul_pow
-- name    : ClassicalComplexWPT.summable_nnnorm_changeOriginSeries_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:52.538235+00:00
-- url     : https://prove2.me/theorems/08c341fc-56ff-472f-81ac-dfc2edeb3573
-- title:
--   Classical Complex WPT: summable nnnorm change Origin Series mul pow
-- statement:
--   The ordinary (Archimedean) majorant needed to sum the weighted coordinate
--   series.  This is extracted from Mathlib's `changeOriginSeries_summable_aux₁`;
--   no ultrametric inequality is used.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L152-L187
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L152-L187

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.summable_nnnorm_changeOriginSeries_mul_pow {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ ‖p.changeOriginSeries k l‖₊ * r ^ k) := by sorry
