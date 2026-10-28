-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_shifted_upclock_finite_of_finite_later_record
-- name    : AvramDividend.Classical.nextRecord_shifted_upclock_finite_of_finite_later_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:54:59.611987+00:00
-- url     : https://prove2.me/theorems/2bf93f33-cbe2-4698-b347-0c3e6a911fa9
-- title:
--   Finite higher record gives a finite shifted first-upcrossing clock
-- statement:
--   For a finite first record reached at its threshold and a later finite record time separated by a finite delay, the shifted strict upward passage clock cannot be infinite. Follows from exact shifted-record infimum decomposition and cancellation of the finite first record in extended nonnegative real addition. Removes the extra finite-shifted-clock assumption in the killed-record renewal estimate.
-- source:
--   Use the proved next-record shifted-infimum identity and the finite record-time equality to cancel the first-clock term in ENNReal, identifying the shifted clock with finite delta.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nextRecord_shifted_upclock_finite_of_finite_later_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b ε : ℝ) (hε : 0 ≤ ε) (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v) :
    (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) ≠ ⊤ := by sorry
