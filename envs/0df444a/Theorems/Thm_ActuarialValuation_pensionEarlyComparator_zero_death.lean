-- Prove2me | Theorems.Thm_ActuarialValuation_pensionEarlyComparator_zero_death
-- name    : ActuarialValuation.pensionEarlyComparator_zero_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T19:23:27.794371+00:00
-- url     : https://prove2.me/theorems/189b1bb3-338d-493a-8ce7-0b74c25f8755
-- title:
--   pensionEarlyComparator zero death
-- statement:
--   Original derived theorem for UK DB pension valuation. The model recovers the pure survivor-to-NRA annuity comparator when there is no pre-commencement death benefit. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   V_{\rm death}=0\Longrightarrow D_E=pv A_N
--   $$
-- source:
--   Original derived result. Per-tranche early retirement and late postponement value routes, early and late factor derivation, pure versus total LRF. UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapters 8-11 and 18, early/late route equations; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapters 9-11 including printed page 68, cashflow reconciliation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyComparator

namespace ActuarialValuation

theorem pensionEarlyComparator_zero_death (p v A : ℝ) :
  pensionEarlyComparator 0 p v A = p * v * A := by sorry

end ActuarialValuation
