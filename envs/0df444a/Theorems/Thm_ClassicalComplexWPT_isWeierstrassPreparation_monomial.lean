-- Prove2me | Theorems.Thm_ClassicalComplexWPT_isWeierstrassPreparation_monomial
-- name    : ClassicalComplexWPT.isWeierstrassPreparation_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:23.255164+00:00
-- url     : https://prove2.me/theorems/ba1db113-e06c-4104-9e9f-167f573f749e
-- title:
--   Classical Complex WPT: is Weierstrass Preparation monomial
-- statement:
--   The monomial is prepared by zero lower coefficients and the constant unit one.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L28-L33
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L28-L33

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.isWeierstrassPreparation_monomial (n d : ℕ) :
    IsWeierstrassPreparation (fun x : Ambient n ↦ x.2 ^ d) d
      (fun _ _ ↦ 0) (fun _ ↦ 1) := by sorry
