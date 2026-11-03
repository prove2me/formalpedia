-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_n_paymentTimes_le_clock
-- name    : AvramDividend.Classical.avram_wave7_08_positive_n_paymentTimes_le_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:51:28.045776+00:00
-- url     : https://prove2.me/theorems/2cd84612-fd48-468c-bb7c-e8f0e79ecf41
-- title:
--   Exact original truncated payment-time region lies before its positive natural clock
-- statement:
--   For the canonical Avram dividend paymentTimes predicate, any eligible payment time under the truncated ENNReal clock min(σ,n) is at or before real time n, provided n is a positive natural. This algebraic support fact is independent of the Lévy law and preserves the actual paymentTimes used by the original source stochastic dividend measure.
-- source:
--   Source-faithful deterministic payment-domain lemma reducing the positive-n and positive-T original UBV finite-clock budget d457be6b-c74a-4a7e-aea2-4bb6222642d5 to the terminal horizon T=n. No substitute process, probability space or cash measure is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_positive_n_paymentTimes_le_clock
    (σ : ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆ Iic (n : ℝ) := by sorry
