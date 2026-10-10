-- Prove2me | Theorems.Thm_ActuarialValuation_alterationRevisedReserve_delta
-- name    : ActuarialValuation.alterationRevisedReserve_delta
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:16:09.34198+00:00
-- url     : https://prove2.me/theorems/f83dbaa9-ef3c-45a0-826d-d4a9bd7fb72c
-- title:
--   Prospective reserve and premium difference: alterationRevisedReserve_delta
-- statement:
--   Change in future premiums shifts the actuarial reserve by the monetised payment difference. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V(P_2)-V(P_1)=(P_1-P_2)a
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationRevisedReserve

namespace ActuarialValuation

theorem alterationRevisedReserve_delta (B A P1 P2 : ℝ) : alterationRevisedReserve B P2 A - alterationRevisedReserve B P1 A = (P1-P2)*A := by sorry

end ActuarialValuation
