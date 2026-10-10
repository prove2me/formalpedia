-- Prove2me | Theorems.Thm_ActuarialValuation_alterationAssetShare_mono_premium
-- name    : ActuarialValuation.alterationAssetShare_mono_premium
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:15:09.263363+00:00
-- url     : https://prove2.me/theorems/2ce613c2-ec03-4bc9-8522-993e2f28f901
-- title:
--   Surrender deductions and policy value comparisons: alterationAssetShare_mono_premium
-- statement:
--   More accumulated premiums increase asset share at a fixed claims and expense base. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p_1\le p_2\Rightarrow AS_1\le AS_2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationAssetShare

namespace ActuarialValuation

theorem alterationAssetShare_mono_premium (p1 p2 outgo : ℝ) (h : p1 ≤ p2) : alterationAssetShare p1 outgo ≤ alterationAssetShare p2 outgo := by sorry

end ActuarialValuation
