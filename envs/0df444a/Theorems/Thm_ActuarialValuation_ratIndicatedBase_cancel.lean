-- Prove2me | Theorems.Thm_ActuarialValuation_ratIndicatedBase_cancel
-- name    : ActuarialValuation.ratIndicatedBase_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:44:21.549359+00:00
-- url     : https://prove2.me/theorems/9e8d2128-b084-4a0f-af76-53ba7af6dbf0
-- title:
--   Base rate calibration and technical premium adequacy: ratIndicatedBase_cancel
-- statement:
--   Indicated base rate exactly recovers target aggregate losses. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   b^*W=T
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratIndicatedBase

namespace ActuarialValuation

theorem ratIndicatedBase_cancel (target w : ℝ) (hw : w ≠ 0) : ratIndicatedBase target w * w = target := by sorry

end ActuarialValuation
