-- Prove2me | Theorems.Thm_ClassicalComplexWPT_isWeierstrassPreparation_nonconstantUnit
-- name    : ClassicalComplexWPT.isWeierstrassPreparation_nonconstantUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:41.099433+00:00
-- url     : https://prove2.me/theorems/fbd472e3-97ba-5948-b092-dabcff5072c4
-- title:
--   Classical Complex WPT: is Weierstrass Preparation nonconstant Unit
-- statement:
--   A nonconstant unit times a prepared degree-one polynomial is still prepared.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L77-L87
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L77-L87

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.isWeierstrassPreparation_nonconstantUnit :
    IsWeierstrassPreparation
      (fun x : Ambient 1 ↦ (1 + x.2) * (x.2 + x.1 0)) 1
      (fun _ z ↦ z 0) (fun x ↦ 1 + x.2) := by sorry
