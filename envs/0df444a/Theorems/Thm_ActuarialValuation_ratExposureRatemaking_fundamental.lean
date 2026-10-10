-- Prove2me | Theorems.Thm_ActuarialValuation_ratExposureRatemaking_fundamental
-- name    : ActuarialValuation.ratExposureRatemaking_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:48:33.771167+00:00
-- url     : https://prove2.me/theorems/1fe778c0-1dfc-43d6-bed3-1c607226a6eb
-- title:
--   Base rate calibration and technical premium adequacy: ratExposureRatemaking_fundamental
-- statement:
--   The substantive pricing capstone establishes unique expected-cost calibration and technical premium adequacy across arbitrary finite risk-class exposures and relativities. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P(b^*)=T,\;b^*\ge0,\;S(b^*)=0,\;b\ge b^*\Rightarrow S(b)\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratWeightedExposure
import Definitions.Def_actuarial_ratPortfolioPremium
import Definitions.Def_actuarial_ratIndicatedBase
import Definitions.Def_actuarial_ratRevenueSurplus

namespace ActuarialValuation

theorem ratExposureRatemaking_fundamental (exposure relativity : ℕ → ℝ) (n : ℕ) (target : ℝ) (hW : 0 < ratWeightedExposure exposure relativity n) (hT : 0 ≤ target) : (ratPortfolioPremium exposure relativity n (ratIndicatedBase target (ratWeightedExposure exposure relativity n)) = target) ∧ (0 ≤ ratIndicatedBase target (ratWeightedExposure exposure relativity n)) ∧ (ratRevenueSurplus target (ratWeightedExposure exposure relativity n) (ratIndicatedBase target (ratWeightedExposure exposure relativity n)) = 0) ∧ (∀ b : ℝ, ratIndicatedBase target (ratWeightedExposure exposure relativity n) ≤ b → 0 ≤ ratRevenueSurplus target (ratWeightedExposure exposure relativity n) b) := by sorry

end ActuarialValuation
