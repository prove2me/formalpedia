-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_lastSlice
-- name    : ClassicalComplexWPT.analyticAt_lastSlice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:21.346139+00:00
-- url     : https://prove2.me/theorems/73a8ec93-7877-44ff-9ea7-c40565c4e9a1
-- title:
--   Classical Complex WPT: analytic At last Slice
-- statement:
--   Restricting an analytic germ to the distinguished-variable axis preserves analyticity.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L17-L23
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L17-L23

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_lastSlice {n : ℕ} {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (lastSlice f) 0 := by sorry
