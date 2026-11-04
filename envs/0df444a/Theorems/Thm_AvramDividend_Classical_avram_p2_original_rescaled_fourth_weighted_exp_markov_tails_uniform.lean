-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_fourth_weighted_exp_markov_tails_uniform
-- name    : AvramDividend.Classical.avram_p2_original_rescaled_fourth_weighted_exp_markov_tails_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:40:26.741986+00:00
-- url     : https://prove2.me/theorems/0b0779d7-9750-4b5c-a333-c4af048b677f
-- title:
--   Original rescaled weighted exponential image has a uniform all-threshold Markov tail envelope
-- statement:
--   On the actual original source and same probability space, there is a finite C such that for all sufficiently small positive h and every nonnegative ENNReal threshold a, a times the inverse-time rescaled fourth-weighted exponential-image measure of marks z at least a is at most C. This directly supplies the compact-exhaustion tail bound for Prokhorov tightness of finite measures; it imports only the independently proved original weighted first-moment Markov bound, and assumes no jump compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_rescaled_fourth_weighted_exp_markov_tails_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ a : ℝ≥0∞,
          a * ((ENNReal.ofReal h)⁻¹ *
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
                {z : ℝ | a ≤ ENNReal.ofReal z}) ≤
          ENNReal.ofReal C := by sorry
