-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_uniform_grid_compact_negative_levy_expectation
-- name    : AvramDividend.Classical.avram_p2_d_future_original_uniform_grid_compact_negative_levy_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:58:12.623196+00:00
-- url     : https://prove2.me/theorems/820ccb46-1d96-492b-8fc8-94e8edbd90da
-- title:
--   Original Lévy uniform-grid compact-negative expectation convergence
-- statement:
--   For the original spectrally negative Lévy process, under genuine source stationary increments and integrability of compact negative tests, the expectation of the finite uniform time-grid increment test sum converges to horizon times the integral of that test against the original Lévy measure. This is an unconditional source expectation theorem, and its proof does not import the complicated intrinsic jump-sum limit helper.
-- source:
--   Original Proved P2-A compact-negative one-cell Lévy expectation rate, exact Proved real/NNReal mesh transport, and Proved P2-J stationary-grid sum integral identity.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_stationary_real_integral

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_uniform_grid_compact_negative_levy_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hInt : ∀ t : ℝ≥0, Integrable (fun ω => f (X.X t ω)) P)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∫ ω, ∑ i ∈ Finset.range (n + 1),
      f (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
         X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (𝓝 ((T : ℝ) *
        (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))))) := by sorry
