-- Prove2me | Theorems.Thm_AllOnesLab_trace_one_allOnes
-- name    : AllOnesLab.trace_one_allOnes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:55:31.720346+00:00
-- url     : https://prove2.me/theorems/1a2b38ad-da0d-4ab2-bcb4-9b9549f046d7
-- title:
--   All Ones Lab: trace one all Ones
-- statement:
--   Trace of 1 in `AdjoinRoot (allOnes n)` is `n` (finrank = n).
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Trace.lean#L69-L76
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Trace.lean#L69-L76

import Definitions.Def_AllOnesLab_Basic
import Definitions.Def_AllOnesLab_Trace
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.trace_one_allOnes (n : ℕ) :
    Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n)) 1 = (n : ZMod 2) := by sorry
