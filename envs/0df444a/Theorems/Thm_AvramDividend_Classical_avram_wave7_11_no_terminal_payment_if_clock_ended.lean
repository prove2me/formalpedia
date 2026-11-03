-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended
-- name    : AvramDividend.Classical.avram_wave7_11_no_terminal_payment_if_clock_ended
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:11:02.266251+00:00
-- url     : https://prove2.me/theorems/0e0c52cb-38a2-4ae3-a76c-69d35629e46a
-- title:
--   Original positive-horizon payment endpoint empty if ruin clock has ended
-- statement:
--   For the canonical original paymentTimes definition and strictly positive real terminal horizon T, if the original stopping clock σ is no later than ENNReal.ofReal T then no dividend payment belongs to the singleton {T}. This excludes spurious terminal dividend atoms when ruin has already occurred.
-- source:
--   Independent endpoint case for exact source-faithful finite-horizon UBV Stieltjes accounting cc518136.

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_no_terminal_payment_if_clock_ended
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T)
    (hσ : σ ≤ ENNReal.ofReal T) :
    paymentTimes σ ∩ {T} = ∅ := by sorry
