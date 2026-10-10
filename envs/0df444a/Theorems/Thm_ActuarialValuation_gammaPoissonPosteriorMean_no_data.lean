-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorMean_no_data
-- name    : ActuarialValuation.gammaPoissonPosteriorMean_no_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:22:38.240963+00:00
-- url     : https://prove2.me/theorems/1efc2c7a-f935-4fb9-8d41-96ed3a5cd06c
-- title:
--   No claim and no exposure data leave the prior mean unchanged
-- statement:
--   With zero recorded claims and zero accumulated exposure, posterior shape and posterior rate each equal their prior values. The predictive expected frequency consequently coincides with the original Gamma prior mean, where β must be positive for a probabilistic interpretation.
--
--   **Mathematical statement**
--
--   $$
--   \hat\lambda(0,0)=\alpha/\beta
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorMean_no_data is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPosteriorMean_no_data (a b : ℝ) :
  gammaPoissonPosteriorMean a b 0 0 = a / b := by sorry

end ActuarialValuation
