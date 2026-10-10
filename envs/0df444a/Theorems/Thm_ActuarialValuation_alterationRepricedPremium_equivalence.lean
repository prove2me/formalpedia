-- Prove2me | Theorems.Thm_ActuarialValuation_alterationRepricedPremium_equivalence
-- name    : ActuarialValuation.alterationRepricedPremium_equivalence
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:11:23.775991+00:00
-- url     : https://prove2.me/theorems/2f766db7-afa9-472a-9f84-340162d1e534
-- title:
--   Prospective reserve and premium difference: alterationRepricedPremium_equivalence
-- statement:
--   A new premium exactly covers future benefit PV when premium annuity is nonzero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_sa=B
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationRepricedPremium

namespace ActuarialValuation

theorem alterationRepricedPremium_equivalence (B A : ℝ) (h : A ≠ 0) : alterationRepricedPremium B A * A = B := by sorry

end ActuarialValuation
