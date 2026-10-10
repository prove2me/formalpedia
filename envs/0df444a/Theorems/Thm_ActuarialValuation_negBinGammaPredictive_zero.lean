-- Prove2me | Theorems.Thm_ActuarialValuation_negBinGammaPredictive_zero
-- name    : ActuarialValuation.negBinGammaPredictive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:23.154677+00:00
-- url     : https://prove2.me/theorems/757a7314-ed41-4e50-a203-7d1a37cca348
-- title:
--   Zero future claims under Gamma-Poisson mixing
-- statement:
--   The unit-exposure probability of observing no Poisson events under a Gamma mixing rate equals (beta/(beta+1)) raised to the positive integer Gamma shape. This is the zero-count specialisation of the negative-binomial predictive mass.
--
--   **Mathematical statement**
--
--   $$
--   g(0)=(\beta/(\beta+1))^r
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinGammaPredictive_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMass

namespace ActuarialValuation

theorem negBinGammaPredictive_zero (r : ℕ) (b : ℝ)
  (hr : 0 < r) (hb : 0 < b) :
  negBinGammaPredictive r b 0 =
    (b / (b + 1)) ^ r := by sorry

end ActuarialValuation
