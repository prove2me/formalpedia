-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_zero_residual_mass_iff_exact_interval_drift_jump
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_zero_residual_mass_iff_exact_interval_drift_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:20:53.30502+00:00
-- url     : https://prove2.me/theorems/21982ac4-0d4e-4668-b629-d9f5f6a34d0e
-- title:
--   Zero actual residual Stieltjes interval mass if and only if exact source drift/jump equality
-- statement:
--   For the unchanged original bounded-variation spectrally negative Levy process, construct a Stieltjes measure whose finite interval mass is exactly the increment of the nondecreasing true physical-drift-minus-original-negative-jumps residual. On one probability-one event and for all s≤t, that residual measure vanishes on (s,t] if and only if the source residual has identical endpoint values, equivalently the true physical drift and actual negative jump increments exactly reconstruct the source process over this interval. This isolates the remaining source-Laplace/rate obligation to force zero residual measure, without assuming the required decomposition.
-- source:
--   Uses proven original residual locally finite atomless Stieltjes measure 4f9a8a4a, monotonicity of the genuine source raw removed residual e9d95081, and ENNReal.ofReal_eq_zero. This is a zero-measure criterion and does not independently establish measure vanishing.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_zero_residual_mass_iff_exact_interval_drift_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        (μ (Ioc a b) = 0 ↔
          (((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) =
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))) := by sorry
