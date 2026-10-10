-- Prove2me | Theorems.Thm_ActuarialValuation_ratClaimsSum_nonneg
-- name    : ActuarialValuation.ratClaimsSum_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:29:26.327671+00:00
-- url     : https://prove2.me/theorems/58a00a65-0ed3-4155-be18-94bb2c843fbc
-- title:
--   Exposure, observed claims and indicated pure premiums: ratClaimsSum_nonneg
-- statement:
--   Nonnegative claims imply nonnegative total observed cost. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   L_i\ge0\Rightarrow L\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClaimsSum

namespace ActuarialValuation

theorem ratClaimsSum_nonneg (l : ℕ → ℝ) (n : ℕ) (hl : ∀ i ∈ Finset.range n, 0 ≤ l i) : 0 ≤ ratClaimsSum l n := by sorry

end ActuarialValuation
