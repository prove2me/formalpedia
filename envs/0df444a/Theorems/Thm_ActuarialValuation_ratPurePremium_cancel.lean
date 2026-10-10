-- Prove2me | Theorems.Thm_ActuarialValuation_ratPurePremium_cancel
-- name    : ActuarialValuation.ratPurePremium_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:30:26.316617+00:00
-- url     : https://prove2.me/theorems/e9b03c25-09e1-403e-ad00-82df38e3e3ad
-- title:
--   Exposure, observed claims and indicated pure premiums: ratPurePremium_cancel
-- statement:
--   Pure premium times exposure reproduces observed claim costs. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (L/E)E=L
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPurePremium

namespace ActuarialValuation

theorem ratPurePremium_cancel (loss exposure : ℝ) (hE : exposure ≠ 0) : ratPurePremium loss exposure * exposure = loss := by sorry

end ActuarialValuation
