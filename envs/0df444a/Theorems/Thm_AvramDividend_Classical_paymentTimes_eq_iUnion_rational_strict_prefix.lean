-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_rational_strict_prefix
-- name    : AvramDividend.Classical.paymentTimes_eq_iUnion_rational_strict_prefix
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T14:06:43.046568+00:00
-- url     : https://prove2.me/theorems/f7c3045b-3219-408b-8c64-433abff06934
-- title:
--   Strict pre-ruin payment times have a countable rational half-open interval exhaustion
-- statement:
--   For every positive possibly infinite ruin time σ, the exact payment-time set [0,σ)∪{0} is the union of half-open intervals [0,r), indexed by positive rational r with ENNReal.ofReal r<σ. This is a countable cofinal family whose endpoints are always strictly before ruin. It includes time zero when σ>0, excludes dividends at positive ruin, and handles σ=∞ without applying toReal to top. This bridges the accepted strict finite-prefix Stieltjes measure equalities to all pre-ruin payments.
-- source:
--   Exact Formalpedia paymentTimes definition, pinned Mathlib ENNReal.ofReal_lt_iff_lt_toReal and exists_rat_btwn; zero-cap verification in Avram et al., 2007 §2-3.

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_eq_iUnion_rational_strict_prefix
    (σ : ℝ≥0∞) (hσ : 0 < σ) :
    paymentTimes σ =
      ⋃ q : {q : ℚ // 0 < ((q : ℚ) : ℝ) ∧
        ENNReal.ofReal ((q : ℚ) : ℝ) < σ},
          Ico (0 : ℝ) ((q : ℚ) : ℝ) := by sorry
