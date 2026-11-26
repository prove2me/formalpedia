-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exactOrderInLastVariable_zero_iff
-- name    : ClassicalComplexWPT.exactOrderInLastVariable_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:19.609817+00:00
-- url     : https://prove2.me/theorems/97b8ed0a-134f-521c-ab09-b29eb7fdd32c
-- title:
--   Classical Complex WPT: exact Order In Last Variable zero iff
-- statement:
--   Exact order zero is exactly nonvanishing at the origin.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L26-L41
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/ExactOrder.lean#L26-L41

import Definitions.Def_ClassicalComplexWPT_Basic
import Mathlib.Analysis.Analytic.Order
import Definitions.Def_ClassicalComplexWPT_ExactOrder
set_option autoImplicit true
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exactOrderInLastVariable_zero_iff {n : ℕ} {f : Ambient n → ℂ} :
    ExactOrderInLastVariable f 0 ↔ f 0 ≠ 0 := by sorry
