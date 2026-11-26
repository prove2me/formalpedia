-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exactOrder_monomial
-- name    : ClassicalComplexWPT.exactOrder_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:17.748299+00:00
-- url     : https://prove2.me/theorems/0f30f57e-6030-57df-b134-130c273dd5c4
-- title:
--   Classical Complex WPT: exact Order monomial
-- statement:
--   The distinguished monomial has exact order `d`; its `d`-th derivative is `d!`.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L17-L25
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L17-L25

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exactOrder_monomial (n d : ℕ) :
    ExactOrderInLastVariable (fun x : Ambient n ↦ x.2 ^ d) d := by sorry
