-- Prove2me | Theorems.Thm_ActuarialValuation_ratClassPremium_nonneg
-- name    : ActuarialValuation.ratClassPremium_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:39:45.643362+00:00
-- url     : https://prove2.me/theorems/a204d0ec-2ffa-467d-b470-bb4055ff6410
-- title:
--   Class relativities and aggregate technical premium: ratClassPremium_nonneg
-- statement:
--   Class pure premium is nonnegative with nonnegative pricing inputs. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e,b,r\ge0\Rightarrow P\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassPremium

namespace ActuarialValuation

theorem ratClassPremium_nonneg (e base rel : ℝ) (he : 0 ≤ e) (hb : 0 ≤ base) (hr : 0 ≤ rel) : 0 ≤ ratClassPremium e base rel := by sorry

end ActuarialValuation
