-- Prove2me | Theorems.Thm_ClassicalComplexWPT_lastTaylorCoefficient_zero
-- name    : ClassicalComplexWPT.lastTaylorCoefficient_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:45.857381+00:00
-- url     : https://prove2.me/theorems/9d2b1295-794f-41de-950b-507b8b1fb285
-- title:
--   Classical Complex WPT: last Taylor Coefficient zero
-- statement:
--   At the base origin, changing origin leaves the diagonal distinguished coefficient unchanged.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L32-L50
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L32-L50

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.lastTaylorCoefficient_zero {n k : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) :
    lastTaylorCoefficient p k 0 = p k (fun _ ↦ lastDirection n) := by sorry
