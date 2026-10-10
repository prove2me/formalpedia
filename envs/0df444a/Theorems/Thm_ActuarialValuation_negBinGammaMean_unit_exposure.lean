-- Prove2me | Theorems.Thm_ActuarialValuation_negBinGammaMean_unit_exposure
-- name    : ActuarialValuation.negBinGammaMean_unit_exposure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:53.246415+00:00
-- url     : https://prove2.me/theorems/5aa7e564-6a48-455c-8c65-c068ef9e094d
-- title:
--   Gamma mixing mean agrees with negative-binomial mean under shape/rate convention
-- statement:
--   The frequency mean for the negative-binomial predictive law derived from a Gamma shape/rate prior at one future exposure is shape divided by rate. This agrees with the prior Gamma mean Poisson intensity, not shape times rate.
--
--   **Mathematical statement**
--
--   $$
--   \mu=r/\beta
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinGammaMean_unit_exposure is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMean
import Definitions.Def_actuarial_negBinGammaProbability

namespace ActuarialValuation

theorem negBinGammaMean_unit_exposure (r : ℕ) (b : ℝ)
  (hb : 0 < b) :
  negBinCountMean r (negBinGammaProbability b) = (r : ℝ) / b := by sorry

end ActuarialValuation
