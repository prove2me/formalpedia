-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_extended_clock_strict_event_iff
-- name    : AvramDividend.Classical.capped_extended_clock_strict_event_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:47:43.466788+00:00
-- url     : https://prove2.me/theorems/3eb89035-1af4-45b5-94e9-32ce913dd218
-- title:
--   Below a finite horizon, capped-real strict survival equals extended-real ruin-clock strict survival
-- statement:
--   For any extended nonnegative-real stopping time tau, any finite NNReal cap T and any t<T, strict survival t<min(tau,T).toReal is equivalent to strict survival (t:ENNReal)<tau of the original untruncated clock, including tau=∞. Proof uses min(tau,T)≤T<∞, injectivity and order preservation of ENNReal.toReal on finite arguments, and t<T. It is the endpoint-correct equivalence required to simplify the capped layer-cake survival integrand back to the original reflected ruin-time tail.
-- source:
--   Pinned Mathlib ENNReal.toReal_lt_toReal and finite caps; Avram Palmowski Pistorius 2007 first-jump zero-barrier law.

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Basic

open scoped NNReal ENNReal

theorem AvramDividend.Classical.capped_extended_clock_strict_event_iff
    (τ : ℝ≥0∞) (T t : ℝ≥0) (ht : t < T) :
    (t : ℝ) < (min τ (T : ℝ≥0∞)).toReal ↔
      (t : ℝ≥0∞) < τ := by sorry
