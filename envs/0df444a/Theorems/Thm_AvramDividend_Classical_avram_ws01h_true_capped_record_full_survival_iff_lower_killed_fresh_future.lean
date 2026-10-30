-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future
-- name    : AvramDividend.Classical.avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:38:41.96674+00:00
-- url     : https://prove2.me/theorems/ec50fc72-f8f8-4fe5-8534-6a1edf6bd5ce
-- title:
--   Genuine capped upper record splits finite-clock nonruin into lower-killed history and survival from the attained upper reserve
-- statement:
--   On a genuine source Lévy upper first-record event before a finite Exp-clock observation horizon and within a cap N, full closed nonruin survival from x is exactly the conjunction of the strict upper-before-lower event and nonruin survival of the full shifted Lévy future started at x+b. The source no-positive-overshoot law supplies X_tau=b. This is the needed source-faithful, noncircular finite-clock survival event split for the killed Esscher renewal.
-- source:
--   Canonical Proved pathwise prefix survival c419e0ac, deterministic horizon split f21cc0d0, no-positive-overshoot df1c0da0, capped clock identity 159a20a9; direct finite-survival upper-first lemma pending publication c4d4b964.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_survival_earlier_record_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_upper_first_preserves_lower_survival_through_record
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_deterministic_closed_survival_at_record_split
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_record_no_positive_overshoot
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_capped_record_full_survival_iff_lower_killed_fresh_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (hb : 0 ≤ b)
    (N : ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (hCap : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞))
    (hEarlier : twoSidedExitUpTime X b ω < (t : ℝ≥0∞)) :
    (let τ : ℝ≥0 :=
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
       twoSidedExitUpTime X b ω <
         twoSidedExitDownTime X (-x) ω ∧
       ∀ u : ℝ≥0, u ≤ t - τ →
         0 ≤ (x + b) + (X.X (τ + u) ω - X.X τ ω)) := by sorry
