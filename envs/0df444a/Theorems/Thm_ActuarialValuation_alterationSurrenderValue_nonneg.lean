-- Prove2me | Theorems.Thm_ActuarialValuation_alterationSurrenderValue_nonneg
-- name    : ActuarialValuation.alterationSurrenderValue_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:09:23.176816+00:00
-- url     : https://prove2.me/theorems/0d1b8e33-94fb-43dd-8d84-c7541c88ffbe
-- title:
--   Surrender deductions and policy value comparisons: alterationSurrenderValue_nonneg
-- statement:
--   The cash surrender amount is nonnegative when charges do not exceed reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c\le V\Rightarrow SV\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

namespace ActuarialValuation

theorem alterationSurrenderValue_nonneg (V c : ℝ) (hc : c ≤ V) : 0 ≤ alterationSurrenderValue V c := by sorry

end ActuarialValuation
