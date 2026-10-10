-- Prove2me | Theorems.Thm_ActuarialValuation_ratRelativity_nonneg
-- name    : ActuarialValuation.ratRelativity_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:33:17.267928+00:00
-- url     : https://prove2.me/theorems/8a2c60b8-c7c3-4bda-9865-fc6103d77d47
-- title:
--   Class relativities and aggregate technical premium: ratRelativity_nonneg
-- statement:
--   Positive reference cost gives nonnegative class relativity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c_i\ge0,c_0>0\Rightarrow r_i\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratRelativity

namespace ActuarialValuation

theorem ratRelativity_nonneg (c base : ℝ) (hc : 0 ≤ c) (hb : 0 < base) : 0 ≤ ratRelativity c base := by sorry

end ActuarialValuation
