-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_finite_grid_weighted_HJB_envelope_scoped
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_predictable_finite_grid_weighted_HJB_envelope_scoped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:38:08.08382+00:00
-- url     : https://prove2.me/theorems/b9dd3411-2021-4fb1-af15-41570b49b33f
-- title:
--   Correctly scoped finite-grid BV predictable HJB generator and dividend corrections
-- statement:
--   For any finite set of actual original controlled predictable reserve left-limit sample times, HJB-interior states, nonnegative physical-time cell weights and dividend-mass cell weights, the joint discounted BV physical drift-plus-compensated-negative-jump generator correction and dividend-density correction have nonpositive finite sum. This applies to deterministic/stopped finite grids and retains the actual source Ω and X; stochastic source-jump compensation and limiting passage remain separate obligations. Each complete combined physical-time and dividend-weighted summand is under the Finset binder; the original first publication omitted this scope in source syntax and is not a valid consumer.
-- source:
--   One accepted exact original predictable-state discounted HJB sign theorem a0879a2f, Finset.sum_nonpos for nonnegative physical time and dividend weights; no synthetic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- Any finite controlled predictable grid has nonpositive discounted BV
physical generator and dividend-density HJB correction when physical-time
and dividend weights are nonnegative and all sampled reserves are interior. -/

theorem AvramDividend.Classical.avram_wave7_02_original_BV_predictable_finite_grid_weighted_HJB_envelope_scoped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : Finset ℝ≥0) (a b : ℝ≥0 → ℝ)
    (ha : ∀ t ∈ u, 0 ≤ a t)
    (hb : ∀ t ∈ u, 0 ≤ b t)
    (hregion : ∀ t ∈ u,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (∑ t ∈ u, (
      a t * (Real.exp (-(q * (t : ℝ))) *
        (X.drift * deriv w (Y t) +
          (∫ z in Iio (0 : ℝ),
            w (Y t + z) - w (Y t) ∂X.ν) - q * w (Y t))) +
      b t * (Real.exp (-(q * (t : ℝ))) *
        (1 - deriv w (Y t))))) ≤ 0 := by sorry
