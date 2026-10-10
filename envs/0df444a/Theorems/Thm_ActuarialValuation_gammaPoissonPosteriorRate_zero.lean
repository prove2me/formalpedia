-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorRate_zero
-- name    : ActuarialValuation.gammaPoissonPosteriorRate_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:21:34.689866+00:00
-- url     : https://prove2.me/theorems/c523124d-ab0e-435a-8fc0-94297f94be9e
-- title:
--   Zero exposure preserves the prior rate
-- statement:
--   When the risk has accumulated no observation exposure, the posterior rate update adds zero. Hence the Gamma prior rate is preserved, independently of any subsequently used claim counts.
--
--   **Mathematical statement**
--
--   $$
--   \beta+0=\beta
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorRate_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPosteriorRate_zero (b : ℝ) :
  gammaPoissonPosteriorRate b 0 = b := by sorry

end ActuarialValuation
