-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountMass_zero_count_parameter
-- name    : ActuarialValuation.negBinCountMass_zero_count_parameter
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:05.897668+00:00
-- url     : https://prove2.me/theorems/358c648a-7ede-459f-94a6-71e14b869b32
-- title:
--   At zero count parameter no positive number of claims occurs
-- statement:
--   With count parameter p equal zero and strictly positive count n, the factor p^n vanishes. This forces the negative-binomial mass at every positive claim count to zero.
--
--   **Mathematical statement**
--
--   $$
--   n>0\Rightarrow f_r(n;p=0)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountMass_zero_count_parameter is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

namespace ActuarialValuation

theorem negBinCountMass_zero_count_parameter (r n : ℕ) (hn : 0 < n) :
  negBinCountMass r 0 n = 0 := by sorry

end ActuarialValuation
