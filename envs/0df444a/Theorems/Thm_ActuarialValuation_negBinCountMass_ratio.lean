-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountMass_ratio
-- name    : ActuarialValuation.negBinCountMass_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:54.008644+00:00
-- url     : https://prove2.me/theorems/89d74719-2264-4737-93de-bb2d9f028ac5
-- title:
--   Neighbouring count coefficients satisfy the negative-binomial Panjer ratio
-- statement:
--   The integer-shape negative-binomial probability coefficients satisfy a stable successor recursion. Multiplying the n+1 count coefficient by n+1 cancels the factorial in the binomial combinatorial ratio and leaves (n+r)p times the n-count coefficient.
--
--   **Mathematical statement**
--
--   $$
--   (n+1)f_r(n+1)=(n+r)pf_r(n)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountMass_ratio is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

namespace ActuarialValuation

theorem negBinCountMass_ratio (r n : ℕ) (p : ℝ)
  (hr : 0 < r) :
  (n + 1 : ℝ) * negBinCountMass r p (n + 1) =
    ((n + r : ℕ) : ℝ) * p * negBinCountMass r p n := by sorry

end ActuarialValuation
