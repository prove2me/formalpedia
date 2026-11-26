-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exactOrder_nonconstantUnit
-- name    : ClassicalComplexWPT.exactOrder_nonconstantUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:43.107663+00:00
-- url     : https://prove2.me/theorems/79101c61-322d-5d30-9d91-81b3e9259844
-- title:
--   Classical Complex WPT: exact Order nonconstant Unit
-- statement:
--   Its distinguished slice has exact order one.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L90-L103
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L90-L103

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exactOrder_nonconstantUnit :
    ExactOrderInLastVariable
      (fun x : Ambient 1 ↦ (1 + x.2) * (x.2 + x.1 0)) 1 := by sorry
