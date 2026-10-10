-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonExperienceWeight_le_one
-- name    : ActuarialValuation.gammaPoissonExperienceWeight_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:24:24.28504+00:00
-- url     : https://prove2.me/theorems/b5decbb4-5c08-4b33-a60e-44f8a55c6521
-- title:
--   Exact Poisson-Gamma credibility weight cannot exceed one
-- statement:
--   The denominator β+E exceeds the nonnegative exposure numerator E by strictly positive prior rate β. Consequently the weight placed on historical experience lies strictly below one for finite positive prior rate.
--
--   **Mathematical statement**
--
--   $$
--   0\le Z<1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonExperienceWeight_le_one is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

namespace ActuarialValuation

theorem gammaPoissonExperienceWeight_le_one
  (b e : ℝ) (hb : 0 < b) (he : 0 ≤ e) :
  gammaPoissonExperienceWeight b e ≤ 1 := by sorry

end ActuarialValuation
