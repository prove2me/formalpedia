-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
-- name    : AvramDividend.Classical.avram_wave7_11_strict_future_clock_preserves_finite_payment_set
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:41:55.780244+00:00
-- url     : https://prove2.me/theorems/e57ac9e9-1cd4-4321-8da3-408eb9bcc0e7
-- title:
--   Exact finite-horizon original dividend payment set under a strictly future auxiliary clock
-- statement:
--   For the exact original dividend paymentTimes convention, if a truncation clock η is strictly later than a given real horizon T, then the dividend payment set through T is exactly unchanged by truncating the original stopping clock σ at η. The strict future condition ensures any dividend right atom at T is retained, unlike truncation precisely at T. Holds for all extended σ and η, including the σ=0 and T=0 branches.
-- source:
--   Original AvramDividend.Classical.paymentTimes definition and ENNReal.ofReal monotonicity; deterministic bridge to UBV finite-horizon value.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_strict_future_clock_preserves_finite_payment_set
    (σ η : ℝ≥0∞) (T : ℝ)
    (hFuture : ENNReal.ofReal T < η) :
    paymentTimes σ ∩ Iic T =
      paymentTimes (min σ η) ∩ Iic T := by sorry
