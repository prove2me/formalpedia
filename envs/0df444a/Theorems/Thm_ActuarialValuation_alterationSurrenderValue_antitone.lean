-- Prove2me | Theorems.Thm_ActuarialValuation_alterationSurrenderValue_antitone
-- name    : ActuarialValuation.alterationSurrenderValue_antitone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:11:02.068394+00:00
-- url     : https://prove2.me/theorems/5c9242c1-5cb5-4b2a-a255-c008283b4bf7
-- title:
--   Surrender deductions and policy value comparisons: alterationSurrenderValue_antitone
-- statement:
--   Increasing a surrender deduction reduces cash paid. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c_1\le c_2\Rightarrow SV(c_2)\le SV(c_1)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

namespace ActuarialValuation

theorem alterationSurrenderValue_antitone (V c1 c2 : ℝ) (h : c1 ≤ c2) : alterationSurrenderValue V c2 ≤ alterationSurrenderValue V c1 := by sorry

end ActuarialValuation
