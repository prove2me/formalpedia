-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_small_negative_exp_quotient_zero
-- name    : AvramDividend.Classical.avram_ja18g_original_small_negative_exp_quotient_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:41:05.413337+00:00
-- url     : https://prove2.me/theorems/42f82199-dff3-4b9f-bae4-e459c3ae9d15
-- title:
--   Compensated small-negative jump exponential quotient vanishes at zero
-- statement:
--   The small compensated jump generator remainder divided by θ tends to 0 for θ↓0. Derive the nonnegative remainder bound ≤θ z²/2 for -1<z<0, integrate using the Lévy small-square condition and squeeze. This only concerns the original ν, no random process replacement.
-- source:
--   J-A18 deterministic original Lévy-Khintchine small-negative derivative

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_small_negative_exp_quotient_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Filter.Tendsto
      (fun θ : ℝ =>
        (∫ z in Ioo (-1 : ℝ) 0,
          (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by sorry
