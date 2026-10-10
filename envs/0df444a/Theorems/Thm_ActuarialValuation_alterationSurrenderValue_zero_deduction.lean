-- Prove2me | Theorems.Thm_ActuarialValuation_alterationSurrenderValue_zero_deduction
-- name    : ActuarialValuation.alterationSurrenderValue_zero_deduction
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:08:09.470528+00:00
-- url     : https://prove2.me/theorems/4d33ce45-e518-4b4e-a584-76857989579d
-- title:
--   Surrender deductions and policy value comparisons: alterationSurrenderValue_zero_deduction
-- statement:
--   With no surrender deduction all available reserve is paid in cash. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c=0\Rightarrow SV=V
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

namespace ActuarialValuation

theorem alterationSurrenderValue_zero_deduction (V : ℝ) : alterationSurrenderValue V 0 = V := by sorry

end ActuarialValuation
