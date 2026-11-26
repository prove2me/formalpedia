-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exactOrder_pow_add_first
-- name    : ClassicalComplexWPT.exactOrder_pow_add_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:34.245339+00:00
-- url     : https://prove2.me/theorems/ba3f39ef-c9c1-5e08-a4af-7408ceaffa49
-- title:
--   Classical Complex WPT: exact Order pow add first
-- statement:
--   For every degree, `w^d + z₀` has exact distinguished-variable order `d`.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L36-L44
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L36-L44

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exactOrder_pow_add_first (d : ℕ) :
    ExactOrderInLastVariable (fun x : Ambient 1 ↦ x.2 ^ d + x.1 0) d := by sorry
