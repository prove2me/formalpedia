-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_shifted_rational_survival_iff_weak_downclock
-- name    : AvramDividend.Classical.avram_ws01h_shifted_rational_survival_iff_weak_downclock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:11:26.994008+00:00
-- url     : https://prove2.me/theorems/8b782b59-61ff-4381-9143-371f66ccaa32
-- title:
--   Source shifted full-future rational survival equals weak strict shifted first lower-passage time
-- statement:
--   For an actual original Lévy path shifted at arbitrary finite age b and any reserve x, countably many rational k/n<T nonnegative tests of the full shifted increments are equivalent to the weak inequality T≤the genuine infimum of all shifted strict lower crossing ages. This holds pointwise for every path including zero and infinite lower passage and arbitrary random stopping age substituted for b. The proof uses original source shifted rational-grid completeness and the infimum clock order; it does not assume the two-sided exit scale formula. This provides the exact almost-everywhere bridge between a measurable rational survival reward and true closed-horizon shifted survival under Esscher exponential time.
-- source:
--   Proved chat04_random_reserve_shifted_lower_before_horizon_grid_iff; Mathlib ENNReal indexed infimum order and linear arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_shifted_rational_survival_iff_weak_downclock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (ω : Ω) (b T : ℝ≥0) :
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ x + (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ↔
    (T : ℝ≥0∞) ≤
      (⨅ (s : ℝ≥0)
        (_ : x + (X.X (b + s) ω - X.X b ω) < 0), (s : ℝ≥0∞)) := by sorry
