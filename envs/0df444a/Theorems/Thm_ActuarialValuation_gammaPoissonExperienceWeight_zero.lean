-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonExperienceWeight_zero
-- name    : ActuarialValuation.gammaPoissonExperienceWeight_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:24:39.186033+00:00
-- url     : https://prove2.me/theorems/af4400e9-849d-4218-894d-977d2eeb03ef
-- title:
--   With zero exposure the Bayesian credibility weight is zero
-- statement:
--   With no observed exposure, the numerator of the exact experience weight is zero. This is the correct limit for reverting to collective prior assumptions and should not be interpreted as a valid finite observed claims-per-exposure ratio at zero exposure.
--
--   **Mathematical statement**
--
--   $$
--   Z(\beta,0)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonExperienceWeight_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

namespace ActuarialValuation

theorem gammaPoissonExperienceWeight_zero (b : ℝ) :
  gammaPoissonExperienceWeight b 0 = 0 := by sorry

end ActuarialValuation
