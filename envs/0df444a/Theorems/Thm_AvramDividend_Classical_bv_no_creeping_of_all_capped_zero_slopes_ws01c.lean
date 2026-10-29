-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_no_creeping_of_all_capped_zero_slopes_ws01c
-- name    : AvramDividend.Classical.bv_no_creeping_of_all_capped_zero_slopes_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:16:53.994753+00:00
-- url     : https://prove2.me/theorems/ad45f4f9-3635-4d66-8c50-77f6fd5c2548
-- title:
--   Bounded-variation strict lower exit cannot creep if all capped post-clock slopes vanish
-- statement:
--   For a standing spectrally negative bounded-variation Lévy process, if the post-clock dyadic drift-deficit slopes vanish almost surely for every integer cap of the actual strict lower exit clock, then the lower-first two-sided exit event almost surely has nonzero terminal reserve. The proof transfers capped zero slopes to a positive right germ at the finite raw clock, restricts to the hypothetical exact contact event, converts positive shifted increments into the required right interval above the lower barrier, and invokes the already Proved conditional-contact no-creeping lemma. This faithfully distinguishes downward jump overshoots from continuous contact.
-- source:
--   Original 50-line complete conditional source work/avram_ws01c_no_creeping_of_cap_slopes_solution_direct.lean, preserving the actual strict lower and upper exit times, finite-clock contact and non-atomic Standing/BV hypotheses. Dependencies canonically Proved: bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c UUID 8a1f87ac-9b56-4f3a-95c4-e94a302c4273 accepted c9a69b94-52e8-4747-acee-ffec857e6478; bv_positive_shifted_increment_contact_right_interval_ws01c UUID e93bf8b1-b8c4-45a5-b7ca-1b1e14423a7b accepted 40bae3cd-ef50-46b9-860c-34ea5eeffbde; conditional no-creeping bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b UUID 6a1ab67e-4996-4ad3-a231-82369673b6a8. This is conditional on explicit all-integer-cap zero-slope hypothesis and does not assert that hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_positive_shifted_increment_contact_right_interval_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_no_creeping_of_all_capped_zero_slopes_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (a x : ℝ) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by sorry
