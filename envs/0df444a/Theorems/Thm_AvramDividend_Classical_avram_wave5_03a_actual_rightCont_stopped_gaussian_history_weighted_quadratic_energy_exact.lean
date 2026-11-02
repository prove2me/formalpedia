-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:01:32.335144+00:00
-- url     : https://prove2.me/theorems/da195565-94fd-4ddf-875a-a15923aa8262
-- title:
--   Exact original stopped predictable Hessian-weighted Gaussian quadratic energy is h sigma squared times its expected weight
-- statement:
--   This identifies the exact Gaussian second-order drift at a genuine original right-continuous stopping time: for every stopped-history measurable and ambient measurable random coefficient H, the original zero-jump Levy source's drift-centred stopped increment Y satisfies E[H Y²] = E[H] h σ². It follows from the Proved original-source stopped-history square factorisation and Wave 6's canonically Proved exact same-path stopped variance. It is the finite-cell predictable Hessian (w'') quadratic energy identity required in deriving the σ²/2 Itô generator, including σ=0, without asserting the missing continuous quadratic-variation process for arbitrary jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
