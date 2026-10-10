-- Prove2me | Theorems.Thm_ActuarialValuation_ratPortfolioPremium_factor
-- name    : ActuarialValuation.ratPortfolioPremium_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:43:58.181619+00:00
-- url     : https://prove2.me/theorems/253f316f-5196-472f-955d-98b829ee0016
-- title:
--   Class relativities and aggregate technical premium: ratPortfolioPremium_factor
-- statement:
--   The class-by-class technical premium sum factors as base rate times weighted exposure. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P=bW
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratWeightedExposure
import Definitions.Def_actuarial_ratPortfolioPremium

namespace ActuarialValuation

theorem ratPortfolioPremium_factor (e r : ℕ → ℝ) (n : ℕ) (base : ℝ) : ratPortfolioPremium e r n base = base * ratWeightedExposure e r n := by sorry

end ActuarialValuation
