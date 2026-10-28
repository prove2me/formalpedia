-- Prove2me | Theorems.Thm_D1Bound5_bennett_factorial_mul_abs_choose
-- name    : D1Bound5.bennett_factorial_mul_abs_choose
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:10.544714+00:00
-- url     : https://prove2.me/theorems/fc90ca7f-34b1-4098-86da-768d64409a87
-- title:
--   Bennett factorial mul abs choose
-- statement:
--   Absolute generalized choose coefficients retain the ordinary factorial denominator and the actual descending Pochhammer numerator.
-- source:
--   D1Bound5/BennettChooseGamma.lean, lines 39-52, SHA-256 ed364c7393e2791f97fcc92aa240c1e9f11c109de4d2306c76becc3f16ded4f0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5






theorem _root_.D1Bound5.bennett_factorial_mul_abs_choose (r : ℝ) (n : ℕ) :
    (n.factorial : ℝ) * |Ring.choose r n| = |(descPochhammer ℝ n).eval r| := by sorry









end D1Bound5
end
