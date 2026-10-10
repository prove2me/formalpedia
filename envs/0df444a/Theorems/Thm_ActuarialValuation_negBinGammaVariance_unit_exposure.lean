-- Prove2me | Theorems.Thm_ActuarialValuation_negBinGammaVariance_unit_exposure
-- name    : ActuarialValuation.negBinGammaVariance_unit_exposure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:08.353206+00:00
-- url     : https://prove2.me/theorems/c63ffa01-1a41-43f4-ba9d-514ebd79881b
-- title:
--   Gamma mixing adds overdispersion to Poisson predictive counts
-- statement:
--   The unit-exposure negative-binomial predictive variance equals the Gamma prior mean Poisson intensity r/b plus the Gamma uncertainty contribution r/b². The extra term explains why the mixed Poisson claim-frequency model is overdispersed.
--
--   **Mathematical statement**
--
--   $$
--   \sigma^2=r/\beta+r/\beta^2
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinGammaVariance_unit_exposure is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountVariance
import Definitions.Def_actuarial_negBinGammaProbability

namespace ActuarialValuation

theorem negBinGammaVariance_unit_exposure (r : ℕ) (b : ℝ)
  (hb : 0 < b) :
  negBinCountVariance r (negBinGammaProbability b) =
    (r : ℝ) / b + (r : ℝ) / b ^ 2 := by sorry

end ActuarialValuation
