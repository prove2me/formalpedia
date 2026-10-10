-- Prove2me | Theorems.Thm_ActuarialValuation_ratRevenueSurplus_monotone
-- name    : ActuarialValuation.ratRevenueSurplus_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:47:35.186975+00:00
-- url     : https://prove2.me/theorems/a3bab3b7-11ca-46c1-9ca6-32ecb7165fd5
-- title:
--   Base rate calibration and technical premium adequacy: ratRevenueSurplus_monotone
-- statement:
--   Revenue surplus increases as the base price increases with nonnegative class mix. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   b_1\le b_2\Rightarrow S_1\le S_2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRevenueSurplus

namespace ActuarialValuation

theorem ratRevenueSurplus_monotone (target w b1 b2 : ℝ) (hw : 0 ≤ w) (h : b1 ≤ b2) : ratRevenueSurplus target w b1 ≤ ratRevenueSurplus target w b2 := by sorry

end ActuarialValuation
