-- Prove2me | Theorems.Thm_ActuarialValuation_alterationPaidUpFraction_le_one
-- name    : ActuarialValuation.alterationPaidUpFraction_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:06:40.70246+00:00
-- url     : https://prove2.me/theorems/67c82fbc-4735-4002-a6b7-a651178015c8
-- title:
--   Paid-up insurance and equivalent cover: alterationPaidUpFraction_le_one
-- statement:
--   If net reserve does not exceed remaining benefit PV, paid-up percentage is at most unity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V\le B,\ B>0\Rightarrow z\le1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpFraction

namespace ActuarialValuation

theorem alterationPaidUpFraction_le_one (V B : ℝ) (hB : 0 < B) (hV : V ≤ B) : alterationPaidUpFraction V B ≤ 1 := by sorry

end ActuarialValuation
