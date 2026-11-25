-- Prove2me | Theorems.Thm_AllOnesLab_trace_root_allOnes
-- name    : AllOnesLab.trace_root_allOnes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:55:07.81063+00:00
-- url     : https://prove2.me/theorems/37575409-ea30-4906-be7f-36026645d4cd
-- title:
--   All Ones Lab: trace root all Ones
-- statement:
--   The root of `allOnes n` in `AdjoinRoot (allOnes n)` has trace 1 (from the Xⁿ⁻¹ coefficient).
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Trace.lean#L53-L64
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Trace.lean#L53-L64

import Definitions.Def_AllOnesLab_Basic
import Definitions.Def_AllOnesLab_Trace
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.trace_root_allOnes (n : ℕ) (hn : 1 ≤ n) :
    Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n)) (AdjoinRoot.root (allOnes n)) = 1 := by sorry
