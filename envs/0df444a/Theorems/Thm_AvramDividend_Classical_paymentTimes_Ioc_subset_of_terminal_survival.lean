-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
-- name    : AvramDividend.Classical.paymentTimes_Ioc_subset_of_terminal_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:27:06.420241+00:00
-- url     : https://prove2.me/theorems/4256f782-3b6d-4b44-adf5-367a4cc593d8
-- title:
--   A nonnegative interval wholly precedes the strict stopped-payment horizon when its upper endpoint survives
-- statement:
--   For the exact dividend payment-time convention used in the Avram Dividend Classical mission, let τ be an extended-nonnegative ruin horizon and 0≤s≤t real interval endpoints. If the upper endpoint embedded as ENNReal.ofReal t is strictly before τ, then every time in (s,t] lies in paymentTimes τ. The proof uses monotonicity of ENNReal.ofReal and the accepted characterisation of paymentTimes at positive ruin horizons. This deterministic endpoint-survival lemma is the precise condition required by the new two-sided stopped Stieltjes record-increment bound and is suitable for first-record and finite-grid interval partitions.
-- source:
--   Accepted paymentTimes_eq_strict_of_pos target 7c01995b-bd0b-43b0-bb5e-3a05fb37de5b; pinned Mathlib ENNReal.ofReal_mono.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_Ioc_subset_of_terminal_survival
    (τ : ℝ≥0∞) (s t : ℝ) (hs : 0 ≤ s)
    (ht : ENNReal.ofReal t < τ) :
    Set.Ioc s t ⊆ paymentTimes τ := by sorry
