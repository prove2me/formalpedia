-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorShape_zero
-- name    : ActuarialValuation.gammaPoissonPosteriorShape_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:21:21.464318+00:00
-- url     : https://prove2.me/theorems/b3aa629a-7114-4eb8-8512-d354834e9d7d
-- title:
--   No observed claims preserve the prior shape
-- statement:
--   When no claims are observed, the sufficient statistic added to the shape is zero. The updated Gamma posterior shape therefore equals its prior shape, even before imposing positivity required by the probabilistic model.
--
--   **Mathematical statement**
--
--   $$
--   \alpha+0=\alpha
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorShape_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape

namespace ActuarialValuation

theorem gammaPoissonPosteriorShape_zero (a : ℝ) :
  gammaPoissonPosteriorShape a 0 = a := by sorry

end ActuarialValuation
