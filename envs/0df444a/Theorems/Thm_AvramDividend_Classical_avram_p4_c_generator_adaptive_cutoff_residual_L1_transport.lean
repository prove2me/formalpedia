-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
-- name    : AvramDividend.Classical.avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:41:21.938647+00:00
-- url     : https://prove2.me/theorems/a87a89b5-94c0-4633-b090-8687acf8646c
-- title:
--   Original discounted stopped generator L1 transport for state-dependent Levy jump cutoffs
-- statement:
--   For an arbitrary original predictable stopped region, reserve u and per-clock cutoff epsilon(p) strictly between zero and one, source generator integrability at each interior state and L1 of its discounted residual imply L1 of the exact physically truncated generator residual and equality of their stopped integrals. The endpoint convention is preserved for each cutoff; no measurability of epsilon is needed because the physical expression equals a measured L1 source expression on the stopped region.
-- source:
--   Source exact original physical truncation 4ca1c36a-241c-4736-9e84-86ee268448ad, stopped generator transport 6e1fd58b-f74d-414a-959b-d75d88923587.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_compact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (ε : α → ℝ)
    (hε : ∀ p ∈ A, 0 < ε p ∧ ε p < 1)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let G : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-(ε p)), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-(ε p)), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-(ε p)) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn G A μ ∧
      (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ) := by sorry
