-- Prove2me | Theorems.Thm_ClassicalComplexWPT_isWeierstrassPreparation_pow_add_first
-- name    : ClassicalComplexWPT.isWeierstrassPreparation_pow_add_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:33.050864+00:00
-- url     : https://prove2.me/theorems/61ab625c-0cd1-5ade-924f-552a8773d48e
-- title:
--   Classical Complex WPT: is Weierstrass Preparation pow add first
-- statement:
--   For positive degree, `w^d + z₀` has the advertised parameter-dependent prepared form.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L47-L74
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Examples.lean#L47-L74

import Definitions.Def_ClassicalComplexWPT_EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Definitions.Def_ClassicalComplexWPT_Examples
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.isWeierstrassPreparation_pow_add_first (d : ℕ) (hd : 0 < d) :
    IsWeierstrassPreparation (fun x : Ambient 1 ↦ x.2 ^ d + x.1 0) d
      (fun i z ↦ if (i : ℕ) = 0 then z 0 else 0) (fun _ ↦ 1) := by sorry
