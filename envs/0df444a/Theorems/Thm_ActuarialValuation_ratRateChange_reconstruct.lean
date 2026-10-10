-- Prove2me | Theorems.Thm_ActuarialValuation_ratRateChange_reconstruct
-- name    : ActuarialValuation.ratRateChange_reconstruct
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:48:00.126489+00:00
-- url     : https://prove2.me/theorems/f75f945c-da67-455a-82b5-e0ddd6e0105f
-- title:
--   Base rate calibration and technical premium adequacy: ratRateChange_reconstruct
-- statement:
--   Relative rate adjustment recovers the proposed base rate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (1+\Delta)b_{old}=b_{new}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRateChange

namespace ActuarialValuation

theorem ratRateChange_reconstruct (old new : ℝ) (h : old ≠ 0) : (1 + ratRateChange new old) * old = new := by sorry

end ActuarialValuation
