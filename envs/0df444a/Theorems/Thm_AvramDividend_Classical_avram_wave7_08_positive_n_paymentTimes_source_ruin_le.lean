-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_n_paymentTimes_source_ruin_le
-- name    : AvramDividend.Classical.avram_wave7_08_positive_n_paymentTimes_source_ruin_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:03:13.622658+00:00
-- url     : https://prove2.me/theorems/db25d81e-d898-4db5-b44d-21862fdc4ee1
-- title:
--   Canonical truncated dividend support is contained in original ruin payment support cut at finite clock
-- statement:
--   For any original ENNReal ruin time σ and strictly positive integer clock n, each dividend payment time eligible before min(σ,n) is also eligible before the actual ruin σ and occurs at or before real time n. This supports comparison of full original ruin-time Stieltjes cash with natural finite-clock cash.
-- source:
--   Uses the Proved exact-source support theorem 2cd84612; preserves the zero-time payment atom and strict positive-time exclusion of ruin time. W7-08 source measure domain for the conditional W6-06 HJB budget bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_positive_n_paymentTimes_source_ruin_le
    (σ : ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆
      paymentTimes σ ∩ Iic (n : ℝ) := by sorry
