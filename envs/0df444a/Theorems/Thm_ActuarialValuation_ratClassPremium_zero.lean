-- Prove2me | Theorems.Thm_ActuarialValuation_ratClassPremium_zero
-- name    : ActuarialValuation.ratClassPremium_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:37:54.39881+00:00
-- url     : https://prove2.me/theorems/84f8d5f8-8c42-4cf8-a7de-815719350e30
-- title:
--   Class relativities and aggregate technical premium: ratClassPremium_zero
-- statement:
--   Zero earned exposure cannot generate technical premium. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P(0,b,r)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium

namespace ActuarialValuation

theorem ratClassPremium_zero (base rel : ℝ) : ratClassPremium 0 base rel = 0 := by sorry

end ActuarialValuation
