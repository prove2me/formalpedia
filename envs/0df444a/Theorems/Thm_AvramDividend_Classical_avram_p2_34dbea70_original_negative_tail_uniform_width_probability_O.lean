-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:33:01.414024+00:00
-- url     : https://prove2.me/theorems/8889c661-983a-4b75-8fd4-618e0d4aa867
-- title:
--   Genuine original Lévy negative-tail cell probability is O(uniform mesh width)
-- statement:
--   For the original spectrally negative Lévy process on its unchanged probability space and every finite positive horizon, evaluate the previously Proved rare-negative-increment probability bound along the actual shrinking uniform grid widths T/(n+1). Obtain a positive real C such that, eventually in n, the probability of an increment at most minus epsilon is bounded by ENNReal.ofReal(C*T/(n+1)). This is a directly source-backed first-moment bound for subsequent genuine grid counting and requires no compensator or rate equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_unweighted_linear_smalltime_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ≤ -ε} ≤
          ENNReal.ofReal (C * ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)) := by sorry
