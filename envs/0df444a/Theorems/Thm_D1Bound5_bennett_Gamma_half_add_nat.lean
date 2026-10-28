-- Prove2me | Theorems.Thm_D1Bound5_bennett_Gamma_half_add_nat
-- name    : D1Bound5.bennett_Gamma_half_add_nat
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:50.68083+00:00
-- url     : https://prove2.me/theorems/2c757065-3c9d-46df-b18c-01dcde153805
-- title:
--   Bennett Gamma half add nat
-- statement:
--   Positive half-integer Gamma values expressed by the actual ascending Pochhammer polynomial. Only Gamma's proved recurrence is used.
-- source:
--   D1Bound5/BennettChooseGamma.lean, lines 12-27, SHA-256 ed364c7393e2791f97fcc92aa240c1e9f11c109de4d2306c76becc3f16ded4f0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5


theorem _root_.D1Bound5.bennett_Gamma_half_add_nat (n : ℕ) :
    Real.Gamma ((1 / 2 : ℝ) + n) =
      Real.Gamma (1 / 2 : ℝ) * (ascPochhammer ℝ n).eval (1 / 2) := by sorry













end D1Bound5
end
