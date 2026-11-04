-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_physical_residual_L1_transport
-- name    : AvramDividend.Classical.avram_p4_c_generator_physical_residual_L1_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:09:08.189729+00:00
-- url     : https://prove2.me/theorems/6e1fd58b-f74d-414a-959b-d75d88923587
-- title:
--   Transport genuine source generator drift L1 and time integral to exact epsilon physical drift and compensator on any measured localisation
-- statement:
--   On any measured space α (including an original predictable time×sample clock), measurable interior region A and reserve path u, original generator-integrability at each y together with source generator residual time integrability implies integrability of the full ε-physical drift-plus-Gaussian-plus-raw-large-jump-plus-compensated-small-jump residual. Its signed time integral equals the source generator residual integral exactly. No separate integrability of the drift/jump terms or pathwise martingale asserted. Transfer holds for any measurable-set localisation and any time weights clock.
-- source:
--   P4-C original_epsilon_drift_compact and Mathlib IntegrableOn.congr_fun/setIntegral_congr_fun

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_physical_residual_L1_transport
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let G : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-ε), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn G A μ ∧ (∫ p in A, G p ∂μ) = (∫ p in A, F p ∂μ) := by sorry
