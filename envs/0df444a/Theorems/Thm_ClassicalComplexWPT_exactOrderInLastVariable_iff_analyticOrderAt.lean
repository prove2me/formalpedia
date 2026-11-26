-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_iff_analyticOrderAt
-- name    : ClassicalComplexWPT.exactOrderInLastVariable_iff_analyticOrderAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:23.739902+00:00
-- url     : https://prove2.me/theorems/85e96814-d313-4811-9cac-f1d90302a09d
-- title:
--   Classical Complex WPT: exact Order In Last Variable iff analytic Order At
-- statement:
--   For an analytic germ, the public derivative condition agrees with Mathlib's analytic order.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L44-L48
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L44-L48

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exactOrderInLastVariable_iff_analyticOrderAt {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ExactOrderInLastVariable f d ↔ analyticOrderAt (lastSlice f) 0 = d := by sorry
