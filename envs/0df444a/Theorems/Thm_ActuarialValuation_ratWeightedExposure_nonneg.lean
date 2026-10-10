-- Prove2me | Theorems.Thm_ActuarialValuation_ratWeightedExposure_nonneg
-- name    : ActuarialValuation.ratWeightedExposure_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:43:17.798667+00:00
-- url     : https://prove2.me/theorems/38870604-1d71-439b-b516-aa1cb9d4d984
-- title:
--   Class relativities and aggregate technical premium: ratWeightedExposure_nonneg
-- statement:
--   Nonnegative class inputs produce nonnegative total weighted exposure. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e_i,r_i\ge0\Rightarrow W\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratWeightedExposure

namespace ActuarialValuation

theorem ratWeightedExposure_nonneg (e r : ℕ → ℝ) (n : ℕ) (he : ∀ i ∈ Finset.range n, 0 ≤ e i) (hr : ∀ i ∈ Finset.range n, 0 ≤ r i) : 0 ≤ ratWeightedExposure e r n := by sorry

end ActuarialValuation
