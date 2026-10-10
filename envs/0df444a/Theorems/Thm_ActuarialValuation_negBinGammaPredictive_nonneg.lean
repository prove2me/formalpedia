-- Prove2me | Theorems.Thm_ActuarialValuation_negBinGammaPredictive_nonneg
-- name    : ActuarialValuation.negBinGammaPredictive_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:36.772814+00:00
-- url     : https://prove2.me/theorems/84b52c38-37de-4276-ae06-ac88dc5bb97c
-- title:
--   Valid Gamma mixing gives nonnegative predictive count coefficients
-- statement:
--   With positive Gamma rate beta, the derived negative-binomial count probability lies strictly between zero and one. Each unit-exposure predictive coefficient is therefore nonnegative by the elementary count-mass sign theorem.
--
--   **Mathematical statement**
--
--   $$
--   \beta>0\Rightarrow g(n)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinGammaPredictive_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaPredictive
import Definitions.Def_actuarial_negBinGammaProbability
import Definitions.Def_actuarial_negBinCountMass

namespace ActuarialValuation

theorem negBinGammaPredictive_nonneg (r n : ℕ) (b : ℝ)
  (hb : 0 < b) :
  0 ≤ negBinGammaPredictive r b n := by sorry

end ActuarialValuation
