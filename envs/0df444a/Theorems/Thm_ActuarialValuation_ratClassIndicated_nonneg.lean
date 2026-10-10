-- Prove2me | Theorems.Thm_ActuarialValuation_ratClassIndicated_nonneg
-- name    : ActuarialValuation.ratClassIndicated_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:30:57.964298+00:00
-- url     : https://prove2.me/theorems/838decdf-00d8-44ed-87d7-7974467bc6b9
-- title:
--   Exposure, observed claims and indicated pure premiums: ratClassIndicated_nonneg
-- statement:
--   Projected frequency/severity technical cost is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f,s\ge0\Rightarrow fs\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 1. Actuarial Standards Board, ASOP 53 Estimating Future Costs for Prospective Property/Casualty Risk Transfer and Risk Retention (2017), Section 3.7, https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/; Casualty Actuarial Society, Basic Ratemaking presentation (2012), https://www.airc.org.tw/newsfiles/BasicRatemakingI.pdf. Parent topic: General insurance loss-cost pricing, exposure-weighted class relativities and exact pure premium calibration. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuarialstandardsboard.org/asops/estimating-future-costs-prospective-propertycasualty-risk-transfer-risk-retention/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratClassIndicated

namespace ActuarialValuation

theorem ratClassIndicated_nonneg (freq severity : ℝ) (hf : 0 ≤ freq) (hs : 0 ≤ severity) : 0 ≤ ratClassIndicated freq severity := by sorry

end ActuarialValuation
