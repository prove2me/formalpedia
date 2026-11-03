-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_adjacent_increment_L2_orthogonal_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_adjacent_increment_L2_orthogonal_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:41:03.061012+00:00
-- url     : https://prove2.me/theorems/b586c633-4adc-4335-8f6e-7c163b9b3ffa
-- title:
--   Adjacent genuine source Gaussian increments are L2 and conditionally orthogonal
-- statement:
--   For the original zero-jump spectrally negative Lévy source X on its physical probability space and right-continuous filtration, and deterministic s≤t≤u, the two adjacent drift-centred increments X_t-X_s-c(t-s) and X_u-X_t-c(u-t) are both L2. Their product is genuinely L1 and has zero conditional expectation given the physical right-continuous past at t. This establishes an adjacent-cell orthogonality building block for same-source predictable simple Gaussian stochastic integral isometry without any auxiliary Brownian copy, with arbitrary sigma including zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_adjacent_increment_L2_orthogonal_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    let Y₁ : Ω → ℝ := fun ω =>
      X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    let Y₂ : Ω → ℝ := fun ω =>
      X.X u ω - X.X t ω - ((u - t) : ℝ) * X.c
    MemLp Y₁ 2 P ∧ MemLp Y₂ 2 P ∧
    Integrable (Y₁ * Y₂) P ∧
      (P[Y₁ * Y₂ | 𝓕.rightCont t] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  sorry
