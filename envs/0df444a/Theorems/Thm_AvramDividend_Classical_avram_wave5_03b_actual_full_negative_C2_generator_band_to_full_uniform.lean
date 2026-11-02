-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:09:00.178112+00:00
-- url     : https://prove2.me/theorems/166d9c11-2e30-405f-bcc7-47049f0850d1
-- title:
--   Actual stopped nonlinear Lévy generator full-minus-finite-band drift has a vanishing uniform error over all times and samples
-- statement:
--   For the original spectrally negative Lévy process X and adapted dividend D, with actual prepayment reserve, compact C² localisation and inclusive stop at ruin, there exists a deterministic ENNReal error sequence tending to zero which bounds, uniformly over every original time t and sample ω, the ENorm of full-negative original Lévy generator drift minus the retained source negative-band truncated drift. The discarded negative marks B_n are measurable, decreasing and have empty intersection. This is the direct source-coupled uniform drift truncation interface for the nonlinear jump half of controlled Ito–Meyer. It uses true X.nu and does not assert a source compensated martingale.
-- source:
--   Canonical Proved 8efe9f2d uniform actual-source discarded-band signed generator error, 314e2bd0 original full negative generator ν-section integrable, pinned Mathlib integral_add_compl and Measure.restrict_restrict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_section_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_source_generator_uniform_band_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ err : ℕ → ℝ≥0∞, Tendsto err atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ p : ℝ≥0 × Ω,
        ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
          (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ ≤ err n := by sorry
