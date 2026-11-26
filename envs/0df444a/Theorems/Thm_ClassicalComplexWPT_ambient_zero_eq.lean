-- Prove2me | Theorems.Thm_ClassicalComplexWPT_ambient_zero_eq
-- name    : ClassicalComplexWPT.ambient_zero_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:04.618737+00:00
-- url     : https://prove2.me/theorems/83459ae7-d6d7-5895-933c-f44b479ac89d
-- title:
--   Classical Complex WPT: ambient zero eq
-- statement:
--   The additive zero in the ambient product is the pair of coordinate zeros.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Basic.lean#L24-L25
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Basic.lean#L24-L25

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_ClassicalComplexWPT_Basic
set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.ambient_zero_eq (n : ℕ) : (0 : Ambient n) = ((0 : Base n), 0) := by sorry
