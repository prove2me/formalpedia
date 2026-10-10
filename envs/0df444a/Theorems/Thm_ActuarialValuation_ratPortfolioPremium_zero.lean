-- Prove2me | Theorems.Thm_ActuarialValuation_ratPortfolioPremium_zero
-- name    : ActuarialValuation.ratPortfolioPremium_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:43:40.445602+00:00
-- url     : https://prove2.me/theorems/61df24d8-b6f5-4ddc-ab7f-c97936b5ce7d
-- title:
--   Class relativities and aggregate technical premium: ratPortfolioPremium_zero
-- statement:
--   No classes means zero technical aggregate premium. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_0=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPortfolioPremium

namespace ActuarialValuation

theorem ratPortfolioPremium_zero (e r : ℕ → ℝ) (base : ℝ) : ratPortfolioPremium e r 0 base = 0 := by sorry

end ActuarialValuation
