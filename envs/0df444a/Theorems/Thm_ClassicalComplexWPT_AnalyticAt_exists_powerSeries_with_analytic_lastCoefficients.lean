-- Prove2me | Theorems.Thm_ClassicalComplexWPT_AnalyticAt_exists_powerSeries_with_analytic_lastCoefficients
-- name    : ClassicalComplexWPT.AnalyticAt.exists_powerSeries_with_analytic_lastCoefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:19.406607+00:00
-- url     : https://prove2.me/theorems/4a4879ef-1161-4a5d-8544-d3a17234a88d
-- title:
--   Analytic At: exists power Series with analytic last Coefficients
-- statement:
--   An analytic germ admits one ambient series whose moving last-variable coefficients are analytic.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L127-L133
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L127-L133

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.AnalyticAt.exists_powerSeries_with_analytic_lastCoefficients
    {n : ℕ} {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ p : FormalMultilinearSeries ℂ (Ambient n) ℂ,
      HasFPowerSeriesAt f p 0 ∧
        ∀ k, AnalyticAt ℂ (lastTaylorCoefficient p k) 0 := by sorry
