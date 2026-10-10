-- Prove2me | Theorems.Thm_ActuarialValuation_negBinCountMass_nonneg
-- name    : ActuarialValuation.negBinCountMass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:39.244819+00:00
-- url     : https://prove2.me/theorems/bcfc27a5-9f21-4e28-9130-1d4b3809b7d7
-- title:
--   Negative-binomial count coefficient nonnegative for valid parameters
-- statement:
--   A natural binomial coefficient, the complement 1−p raised to a natural power, and p raised to a natural power are nonnegative when p lies in the unit interval. The shape can be any natural for this sign lemma, although the conventional probability model requires r>0.
--
--   **Mathematical statement**
--
--   $$
--   0\le p\le1\Rightarrow f_r(n)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinCountMass_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

namespace ActuarialValuation

theorem negBinCountMass_nonneg (r n : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
  0 ≤ negBinCountMass r p n := by sorry

end ActuarialValuation
