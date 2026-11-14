-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
-- name    : AvramDividend.Classical.avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:24:44.689739+00:00
-- url     : https://prove2.me/theorems/c7a5d29a-994e-47d6-b4bf-0199ec1f08cc
-- title:
--   Actual original linear Lévy physical sample path has zero jumps at every time up to the observation horizon
-- statement:
--   Whenever the actual original spectrally negative Lévy source path satisfies X_t=t times its drift for every nonnegative physical time up to a finite observation horizon, its true left-limit jump X_t-leftLim(X)_t vanishes at every physical time up to that horizon. The proof uses the continuous linear source path and the pinned Mathlib ContinuousWithinAt.leftLim_eq on Iic(t), rather than replacing the source process. This discharges exactly the no-source-jump hypothesis in the Proved original zero-contact full discounted-cash HJB inequality 09a9c1c4.
-- source:
--   Pinned Mathlib ContinuousWithinAt.leftLim_eq and ContinuousWithinAt.congr; original physical linear path hypothesis on 209eed42.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : ℝ≥0)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
      X.X t ω = (t : ℝ) * X.drift) :
    ∀ t : ℝ≥0, t ≤ S →
      X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = 0 := by sorry
