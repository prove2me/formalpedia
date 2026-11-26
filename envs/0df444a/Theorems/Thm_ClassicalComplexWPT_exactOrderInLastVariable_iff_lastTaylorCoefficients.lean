-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_iff_lastTaylorCoefficients
-- name    : ClassicalComplexWPT.exactOrderInLastVariable_iff_lastTaylorCoefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:17.710966+00:00
-- url     : https://prove2.me/theorems/63d80b23-410f-4c25-afce-a8fee70f053c
-- title:
--   Classical Complex WPT: exact Order In Last Variable iff last Taylor Coefficients
-- statement:
--   The public exact-order condition is exactly the first-nonzero-coefficient condition.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L91-L107
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L91-L107

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exactOrderInLastVariable_iff_lastTaylorCoefficients {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    ExactOrderInLastVariable f d ↔
      (∀ k < d, lastTaylorCoefficient p k 0 = 0) ∧
        lastTaylorCoefficient p d 0 ≠ 0 := by sorry
