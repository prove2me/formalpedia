-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_positive_event_all_original_short_meshes_centered_noise_uniform
-- name    : AvramDividend.Classical.avram_gaussianB_positive_event_all_original_short_meshes_centered_noise_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:21:26.022213+00:00
-- url     : https://prove2.me/theorems/1243998f-a2ba-4c3e-b9a1-37ee6e52bbcd
-- title:
--   A genuine positive-probability Gaussian event simultaneously bounds every sufficiently fine original stopped centred physical-grid noise sum
-- statement:
--   There exists a real original drift-two, variance-one, zero-jump spectrally negative Lévy model with Standing, UBV and admissible equal-cap dividend strategy, and a measurable positive-probability Gaussian event E such that for every ω in E and every physical grid m≥15999, the actual original discounted stopped centred source sum has absolute value at most 1/4000. This is the finite-grid martingale noise bound needed to transfer the original fixed-band cash contradiction to an L¹ limit.

import Mathlib.Tactic.NormNum
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_positive_event_all_original_short_meshes_centered_noise_uniform
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E, ∀ m : ℕ, 15999 ≤ m →
          let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
          let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
          |(Finset.range (m + 1)).sum (fun i =>
            if s i < (1 / 1000 : ℝ≥0) then
              Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
                (Y.X (s (i + 1)) ω - Y.X (s i) ω -
                  ((s (i + 1) : ℝ) - (s i : ℝ)) * Y.c)
            else 0)| ≤ (1 / 4000 : ℝ) := by sorry
