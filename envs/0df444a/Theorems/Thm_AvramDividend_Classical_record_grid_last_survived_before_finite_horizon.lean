-- Prove2me | Theorems.Thm_AvramDividend_Classical_record_grid_last_survived_before_finite_horizon
-- name    : AvramDividend.Classical.record_grid_last_survived_before_finite_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:26:51.1839+00:00
-- url     : https://prove2.me/theorems/8f3d8f67-11ec-490b-8e43-630b13fdd0b1
-- title:
--   Every finite horizon has no first record or a final attained grid record
-- statement:
--   Fix a positive record spacing and any finite observation horizon T, independently of whether dividend ruin is finite or infinite. Either the first positive record threshold has not been crossed strictly before T, or some last grid threshold b+n h is crossed strictly before T while the next threshold is not. A finite-horizon path is bounded above, so sufficiently high record clocks lie beyond T; the conclusion then follows by induction on the grid index. This supplies a finite truncation for global stopped-renewal upper estimates.
-- source:
--   Direct consequence of the accepted eventual finite-horizon record-clock bound, with finite induction to select the final strict pre-horizon crossing.

import Mathlib.Data.Nat.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.record_grid_last_survived_before_finite_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b h : ℝ) (hh : 0 < h) (T : ℝ≥0) :
    (¬ (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) <
      (T : ℝ≥0∞)) ∨
    ∃ n : ℕ,
      (⨅ (r : ℝ≥0)
        (_ : b + (n : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
        (T : ℝ≥0∞) ∧
      ¬ (⨅ (r : ℝ≥0)
        (_ : b + ((n + 1 : ℕ) : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
        (T : ℝ≥0∞) := by sorry
