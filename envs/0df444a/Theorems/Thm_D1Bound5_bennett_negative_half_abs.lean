-- Prove2me | Theorems.Thm_D1Bound5_bennett_negative_half_abs
-- name    : D1Bound5.bennett_negative_half_abs
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:14.674087+00:00
-- url     : https://prove2.me/theorems/2bffe54f-4ce2-424b-81b6-cf0e1b2ac39c
-- title:
--   Bennett negative half abs
-- statement:
--   The absolute negative-half tail is the same positive ascending product.
-- source:
--   D1Bound5/BennettChooseGamma.lean, lines 64-74, SHA-256 ed364c7393e2791f97fcc92aa240c1e9f11c109de4d2306c76becc3f16ded4f0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5










theorem _root_.D1Bound5.bennett_negative_half_abs (m : ℕ) :
    (m.factorial : ℝ) * |Ring.choose (-1 / 2 : ℝ) m| =
      (ascPochhammer ℝ m).eval (1 / 2) := by sorry





end D1Bound5
end
