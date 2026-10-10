-- Prove2me | Theorems.Thm_ActuarialValuation_negBinGammaProbability_pos
-- name    : ActuarialValuation.negBinGammaProbability_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:28:52.44852+00:00
-- url     : https://prove2.me/theorems/12ec83e7-0c18-49a4-9695-bced2397eaca
-- title:
--   Positive Gamma rate gives a positive predictive count parameter
-- statement:
--   Prior Gamma rate b positive implies denominator b+1 strictly positive, so its reciprocal is a valid strictly positive negative-binomial count parameter.
--
--   **Mathematical statement**
--
--   $$
--   \beta>0\Rightarrow p>0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.5, printed page 383 (Library PDF page 409), parent framework: Section 21.5 (negative-binomial frequency). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://encyclopediaofmath.org/wiki/Negative_binomial_distribution. The specific Lean declaration ActuarialValuation.negBinGammaProbability_pos is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinGammaProbability

namespace ActuarialValuation

theorem negBinGammaProbability_pos (b : ℝ) (hb : 0 < b) :
  0 < negBinGammaProbability b := by sorry

end ActuarialValuation
