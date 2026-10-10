-- Prove2me | Theorems.Thm_ActuarialValuation_alterationReserveRelease_equals_deduction
-- name    : ActuarialValuation.alterationReserveRelease_equals_deduction
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:11:18.348905+00:00
-- url     : https://prove2.me/theorems/313af355-8444-47f8-a345-9066352a5e11
-- title:
--   Surrender deductions and policy value comparisons: alterationReserveRelease_equals_deduction
-- statement:
--   Reserve released less cash surrender value equals the explicit deduction. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V-SV=c
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue
import Definitions.Def_actuarial_alterationReserveRelease

namespace ActuarialValuation

theorem alterationReserveRelease_equals_deduction (V c : ℝ) : alterationReserveRelease V (alterationSurrenderValue V c) = c := by sorry

end ActuarialValuation
