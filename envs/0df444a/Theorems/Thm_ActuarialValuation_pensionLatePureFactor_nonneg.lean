-- Prove2me | Theorems.Thm_ActuarialValuation_pensionLatePureFactor_nonneg
-- name    : ActuarialValuation.pensionLatePureFactor_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T19:24:04.705394+00:00
-- url     : https://prove2.me/theorems/58865427-4078-4548-a099-581d960a3a19
-- title:
--   pensionLatePureFactor nonneg
-- statement:
--   Original derived theorem for UK DB pension valuation. The net value available for deferred pension is nonnegative once factor-independent death costs are deducted. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   N\ge D,\ pv m A>0\Longrightarrow F_L\ge0
--   $$
-- source:
--   Original derived result. Per-tranche early retirement and late postponement value routes, early and late factor derivation, pure versus total LRF. UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapters 8-11 and 18, early/late route equations; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapters 9-11 including printed page 68, cashflow reconciliation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePureFactor

namespace ActuarialValuation

theorem pensionLatePureFactor_nonneg (N D p v m A : ℝ)
  (hN : D ≤ N) (hden : 0 < p * v * m * A) :
  0 ≤ pensionLatePureFactor N D p v m A := by sorry

end ActuarialValuation
