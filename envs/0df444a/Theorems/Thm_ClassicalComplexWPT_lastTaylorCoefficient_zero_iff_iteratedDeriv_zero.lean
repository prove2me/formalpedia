-- Prove2me | Theorems.Thm_ClassicalComplexWPT_lastTaylorCoefficient_zero_iff_iteratedDeriv_zero
-- name    : ClassicalComplexWPT.lastTaylorCoefficient_zero_iff_iteratedDeriv_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:00.09127+00:00
-- url     : https://prove2.me/theorems/a62fb75b-9b37-5d36-a970-bd0ddec7b89e
-- title:
--   Classical Complex WPT: last Taylor Coefficient zero iff iterated Deriv zero
-- statement:
--   Vanishing of a directional Taylor coefficient is equivalent to vanishing of the derivative.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L83-L88
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L83-L88

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.lastTaylorCoefficient_zero_iff_iteratedDeriv_zero {n k : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    lastTaylorCoefficient p k 0 = 0 ↔ iteratedDeriv k (lastSlice f) 0 = 0 := by sorry
