-- Prove2me | Theorems.Thm_ActuarialValuation_pensionLatePostponedValue_zero_factor
-- name    : ActuarialValuation.pensionLatePostponedValue_zero_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T19:23:37.902983+00:00
-- url     : https://prove2.me/theorems/390dc3c1-11ab-4153-9d5c-e19a11f47882
-- title:
--   pensionLatePostponedValue zero factor
-- statement:
--   Original derived theorem for UK DB pension valuation. Factor-independent postponement death benefits remain even if the eventual pension payment factor is zero. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   F_L=0\Longrightarrow V_L=V_{\rm death}
--   $$
-- source:
--   Original derived result. Per-tranche early retirement and late postponement value routes, early and late factor derivation, pure versus total LRF. UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapters 8-11 and 18, early/late route equations; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapters 9-11 including printed page 68, cashflow reconciliation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePostponedValue

namespace ActuarialValuation

theorem pensionLatePostponedValue_zero_factor (D p v m A : ℝ) :
  pensionLatePostponedValue D p v m A 0 = D := by sorry

end ActuarialValuation
