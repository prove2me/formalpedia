-- Prove2me | Theorems.Thm_ActuarialValuation_negBinGammaProbability_lt_one
-- name    : ActuarialValuation.negBinGammaProbability_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:09.212786+00:00
-- url     : https://prove2.me/theorems/1fe9677e-b5b0-4d91-a933-b8e38c764984
-- title:
--   Positive Gamma rate makes the predictive count parameter below one
-- statement:
--   Because the positive Gamma rate makes beta plus one strictly larger than one, the count parameter p=1/(beta+1) is strictly less than one.
--
--   **Mathematical statement**
--
--   $$
--   \beta>0\Rightarrow p<1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinGammaProbability_lt_one is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaProbability

namespace ActuarialValuation

theorem negBinGammaProbability_lt_one (b : ℝ) (hb : 0 < b) :
  negBinGammaProbability b < 1 := by sorry

end ActuarialValuation
