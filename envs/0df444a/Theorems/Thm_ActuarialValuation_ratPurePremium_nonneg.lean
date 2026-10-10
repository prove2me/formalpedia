-- Prove2me | Theorems.Thm_ActuarialValuation_ratPurePremium_nonneg
-- name    : ActuarialValuation.ratPurePremium_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:30:42.110014+00:00
-- url     : https://prove2.me/theorems/e113da57-c073-4b98-a70c-1be3ddd874c0
-- title:
--   Exposure, observed claims and indicated pure premiums: ratPurePremium_nonneg
-- statement:
--   Positive earned exposure and nonnegative costs give nonnegative indicated price. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   L\ge0,E>0\Rightarrow c\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPurePremium

namespace ActuarialValuation

theorem ratPurePremium_nonneg (loss exposure : ℝ) (hL : 0 ≤ loss) (hE : 0 < exposure) : 0 ≤ ratPurePremium loss exposure := by sorry

end ActuarialValuation
