-- Prove2me | Theorems.Thm_ActuarialValuation_alterationPaidUpScaledValue_add
-- name    : ActuarialValuation.alterationPaidUpScaledValue_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:07:57.378495+00:00
-- url     : https://prove2.me/theorems/df5beea6-d3ae-4172-8dd2-5acfce09ba41
-- title:
--   Paid-up insurance and equivalent cover: alterationPaidUpScaledValue_add
-- statement:
--   Paid-up proportional benefit values are additive over cover portions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PV(f+g)=PV(f)+PV(g)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpScaledValue

namespace ActuarialValuation

theorem alterationPaidUpScaledValue_add (f g B : ℝ) : alterationPaidUpScaledValue (f+g) B = alterationPaidUpScaledValue f B + alterationPaidUpScaledValue g B := by sorry

end ActuarialValuation
