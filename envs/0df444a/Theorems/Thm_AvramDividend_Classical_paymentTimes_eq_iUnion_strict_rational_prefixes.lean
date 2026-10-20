-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_strict_rational_prefixes
-- name    : AvramDividend.Classical.paymentTimes_eq_iUnion_strict_rational_prefixes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:43:58.835574+00:00
-- url     : https://prove2.me/theorems/bd59652c-b28d-4766-840c-d07855f05d48
-- title:
--   Strictly pre-ruin payment times have a countable cofinal family of rational half-open prefixes
-- statement:
--   For any positive ruin horizon sigma in extended nonnegative reals, the exact paymentTimes set [0,sigma)∪{0} equals the union of all real intervals [0,q) where q ranges over positive rationals satisfying ofReal(q)<sigma. This covers both finite positive and infinite ruin horizons without using toReal infinity. The proof uses rational density below the finite endpoint and unbounded rational numbers when sigma is infinite. The zero horizon sigma=0 is excluded and handled by the separately proved zero initial payment atom lemma.
-- source:
--   Exact published Avram DividendStrategy paymentTimes definition, pinned Mathlib Data.ENNReal.Real ofReal_lt_iff_lt_toReal and Archimedean exists_rat_btwn.

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_eq_iUnion_strict_rational_prefixes
    (σ : ℝ≥0∞) (hσ : 0 < σ) :
    paymentTimes σ =
      ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < σ},
        Ico (0 : ℝ) (q.val : ℝ) := by sorry
