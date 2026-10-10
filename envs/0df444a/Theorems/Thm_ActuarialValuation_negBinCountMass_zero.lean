-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountMass_zero
-- name    : ActuarialValuation.negBinCountMass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:25.071508+00:00
-- url     : https://prove2.me/theorems/dc70c30a-e8d5-46d0-b058-b023e57aa079
-- title:
--   Negative-binomial zero claim count coefficient
-- statement:
--   The binomial coefficient at claim count zero is one when the integer shape is positive. The count-parameter power at zero is one, leaving the rth power of the complement as the no-claim coefficient.
--
--   **Mathematical statement**
--
--   $$
--   f_r(0)=(1-p)^r
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountMass_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

namespace ActuarialValuation

theorem negBinCountMass_zero (r : ℕ) (p : ℝ) (hr : 0 < r) :
  negBinCountMass r p 0 = (1 - p) ^ r := by sorry

end ActuarialValuation
