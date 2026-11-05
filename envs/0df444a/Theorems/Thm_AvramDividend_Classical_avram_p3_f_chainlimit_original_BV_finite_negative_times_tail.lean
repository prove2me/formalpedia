-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_BV_finite_negative_times_tail
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_BV_finite_negative_times_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:32:54.238165+00:00
-- url     : https://prove2.me/theorems/0b53d65a-d9f5-4f84-b2da-e234b6b93864
-- title:
--   Actual original BV source finite strict negative jump times capture all but epsilon total jump mass
-- statement:
--   For the genuine original bounded-variation spectrally negative Lévy process, almost every source path admits, for every positive epsilon, a finite set of strictly positive jump times within the real horizon, outside which the sum of original negative-left-jump magnitudes is smaller than epsilon. This is a source-specific finite marking interface for P3-F mesh construction, independent of compensation, dividends or generator sign.
-- source:
--   Proved almost-sure original source small-jump epsilon cutoff 3a4709e5 and Proved original finite strict large-mark times 2f296cf8; choose the finite threshold set and identify its complementary tsum with the small-cutoff tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_small_jump_epsilon_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_finite_strict_large_marks
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_BV_finite_negative_times_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let j : ℝ≥0 → ℝ := fun u =>
        if 0 < u ∧ u ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0
      ∀ ε : ℝ, 0 < ε →
        ∃ S : Finset ℝ≥0,
          (∀ t, t ∈ S → 0 < t ∧ t ≤ T) ∧
          (∑' t : ℝ≥0, if t ∈ S then 0 else |j t|) < ε := by sorry
