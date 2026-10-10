-- Prove2me | Theorems.Thm_ActuarialValuation_alterationReserve_balance
-- name    : ActuarialValuation.alterationReserve_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:06:24.875884+00:00
-- url     : https://prove2.me/theorems/0c018dcf-afe5-42e6-8574-030e8ebfebf0
-- title:
--   Prospective reserve and premium difference: alterationReserve_balance
-- statement:
--   Reserve and future premium income PV reconcile to future expected benefit outgo. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V+Pa=B
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve

namespace ActuarialValuation

theorem alterationReserve_balance (B A P : ℝ) : alterationProspectiveReserve B A P + P*A = B := by sorry

end ActuarialValuation
