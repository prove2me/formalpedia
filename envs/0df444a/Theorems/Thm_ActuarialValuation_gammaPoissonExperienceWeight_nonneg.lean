-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonExperienceWeight_nonneg
-- name    : ActuarialValuation.gammaPoissonExperienceWeight_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:24:01.763845+00:00
-- url     : https://prove2.me/theorems/6dac046b-67f4-4782-a898-a6d85685f94e
-- title:
--   Exact Poisson-Gamma credibility weight is nonnegative
-- statement:
--   Observed exposure is nonnegative and prior rate is positive, so both the credibility numerator and its posterior-rate denominator have nonnegative or positive sign respectively. The experience weight is therefore nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \beta>0,E\ge0\Rightarrow Z\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonExperienceWeight_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

namespace ActuarialValuation

theorem gammaPoissonExperienceWeight_nonneg
  (b e : ℝ) (hb : 0 < b) (he : 0 ≤ e) :
  0 ≤ gammaPoissonExperienceWeight b e := by sorry

end ActuarialValuation
