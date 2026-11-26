-- Prove2me | Theorems.Thm_ClassicalComplexWPT_factorial_smul_lastTaylorCoefficient_zero
-- name    : ClassicalComplexWPT.factorial_smul_lastTaylorCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:57.256387+00:00
-- url     : https://prove2.me/theorems/9b302a89-5612-5779-803f-616412b747ec
-- title:
--   Classical Complex WPT: factorial smul last Taylor Coefficient zero
-- statement:
--   The moving coefficient at the base origin is the usual factorial-normalized
--   iterated derivative of the distinguished slice.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L56-L80
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L56-L80

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.factorial_smul_lastTaylorCoefficient_zero {n k : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    k.factorial • lastTaylorCoefficient p k 0 =
      iteratedDeriv k (lastSlice f) 0 := by sorry
