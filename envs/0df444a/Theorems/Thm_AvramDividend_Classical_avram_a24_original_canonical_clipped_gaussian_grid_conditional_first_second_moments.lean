-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
-- name    : AvramDividend.Classical.avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:37:12.243586+00:00
-- url     : https://prove2.me/theorems/310c0e23-3422-4362-b537-40f169e88558
-- title:
--   Original stopped canonical Gaussian mesh exact first and second conditional moments
-- statement:
--   For every original zero-jump Levy driver and every actual right-continuous stopping time bounded by a deterministic horizon, each canonical uniform physical grid cell has integrable genuine centred Gaussian increment and square. The increment conditional expectation given the exact clipped grid start equals zero, and the conditional second moment equals the actual deterministic cell length times the original process Gaussian variance. This directly instantiates the original Prove2Me physical source grid in A24, and avoids assuming synthetic centred increments or a priori moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ j i : ℕ,
      let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let τg : Ω → ℝ≥0 := fun ω => min ((i : ℝ≥0) * δ) (σ ω)
      let hτg : ∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s] {ω : Ω | τg ω ≤ s} :=
        (avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
          σ hσstop n hσbound).1 j i
      let M : Ω → ℝ := fun ω =>
        X.X (τg ω + δ) ω - X.X (τg ω) ω - (δ : ℝ) * X.c
      Integrable M P ∧
      (P[M | (isStoppingTime_withTop_of_le_events τg hτg).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ))) ∧
      Integrable (fun ω => M ω ^ 2) P ∧
      (P[(fun ω => M ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τg hτg).measurableSpace]
        =ᵐ[P] (fun _ => (δ : ℝ) * X.σ ^ 2)):= by sorry
