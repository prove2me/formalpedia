-- Prove2me | Theorems.Thm_ActuarialValuation_alterationSurrenderValue_le_reserve
-- name    : ActuarialValuation.alterationSurrenderValue_le_reserve
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:09:07.201053+00:00
-- url     : https://prove2.me/theorems/af735252-a541-4552-8607-cd4409ea45e6
-- title:
--   Surrender deductions and policy value comparisons: alterationSurrenderValue_le_reserve
-- statement:
--   A nonnegative surrender charge prevents cash paid from exceeding reserves. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c\ge0\Rightarrow SV\le V
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

namespace ActuarialValuation

theorem alterationSurrenderValue_le_reserve (V c : ℝ) (hc : 0 ≤ c) : alterationSurrenderValue V c ≤ V := by sorry

end ActuarialValuation
