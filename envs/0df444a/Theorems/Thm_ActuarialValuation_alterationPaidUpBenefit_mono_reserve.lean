-- Prove2me | Theorems.Thm_ActuarialValuation_alterationPaidUpBenefit_mono_reserve
-- name    : ActuarialValuation.alterationPaidUpBenefit_mono_reserve
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:06:19.491259+00:00
-- url     : https://prove2.me/theorems/299a0594-dac9-4482-89ab-f78e5bd7e967
-- title:
--   Paid-up insurance and equivalent cover: alterationPaidUpBenefit_mono_reserve
-- statement:
--   Greater reserve permits a larger paid-up insurance sum assured. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_1\le V_2\Rightarrow b_1\le b_2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpBenefit

namespace ActuarialValuation

theorem alterationPaidUpBenefit_mono_reserve (V1 V2 A : ℝ) (hA : 0 < A) (h : V1 ≤ V2) : alterationPaidUpBenefit V1 A ≤ alterationPaidUpBenefit V2 A := by sorry

end ActuarialValuation
