-- Prove2me | Theorems.Thm_D1Bound5_bennett_ascPochhammer_half_pos
-- name    : D1Bound5.bennett_ascPochhammer_half_pos
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:46.446391+00:00
-- url     : https://prove2.me/theorems/7320939b-c7b7-4224-825e-e6bed6ae80db
-- title:
--   Bennett asc Pochhammer half pos
-- statement:
--   Auxiliary result `bennett_ascPochhammer_half_pos` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettChooseGamma.lean, lines 29-37, SHA-256 ed364c7393e2791f97fcc92aa240c1e9f11c109de4d2306c76becc3f16ded4f0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5



theorem _root_.D1Bound5.bennett_ascPochhammer_half_pos (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (1 / 2) := by sorry











end D1Bound5
end
