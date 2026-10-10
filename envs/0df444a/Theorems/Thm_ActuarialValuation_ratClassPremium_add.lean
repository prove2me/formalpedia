-- Prove2me | Theorems.Thm_ActuarialValuation_ratClassPremium_add
-- name    : ActuarialValuation.ratClassPremium_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:40:10.592978+00:00
-- url     : https://prove2.me/theorems/4de7701a-9817-4734-9348-914a1e397a54
-- title:
--   Class relativities and aggregate technical premium: ratClassPremium_add
-- statement:
--   Combining same-risk-class exposures preserves total technical premium. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P(e_1+e_2)=P(e_1)+P(e_2)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium

namespace ActuarialValuation

theorem ratClassPremium_add (e1 e2 base rel : ℝ) : ratClassPremium (e1+e2) base rel = ratClassPremium e1 base rel + ratClassPremium e2 base rel := by sorry

end ActuarialValuation
