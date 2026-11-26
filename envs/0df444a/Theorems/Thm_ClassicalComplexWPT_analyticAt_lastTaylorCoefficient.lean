-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_lastTaylorCoefficient
-- name    : ClassicalComplexWPT.analyticAt_lastTaylorCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:59.482625+00:00
-- url     : https://prove2.me/theorems/819f8b3c-740a-5f2b-9a39-70729f2856d1
-- title:
--   Classical Complex WPT: analytic At last Taylor Coefficient
-- statement:
--   Every moving distinguished-variable coefficient is analytic in the base variables.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L110-L124
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L110-L124

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_lastTaylorCoefficient {n k : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : 0 < p.radius) :
    AnalyticAt ℂ (lastTaylorCoefficient p k) 0 := by sorry
