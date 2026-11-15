-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45_interior_BV_source_HJB_to_derivative_loss_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB45_interior_BV_source_HJB_to_derivative_loss_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:14:12.924014+00:00
-- url     : https://prove2.me/theorems/a7cc5dab-90ef-45dd-90dc-261b20d193c1
-- title:
--   Interior BV generator HJB inequality implies derivative-loss envelope
-- statement:
--   For a bounded-variation spectrally negative Lévy process, the generator supersolution inequality on the strict interior and an upper bound for q*w, combined with the negative-jump derivative-loss majorant, imply a drift-times-gradient bound on every point strictly inside the tested interval. This is the sound interior version of the existing statement whose conclusion included endpoints excluded by its generator premise.
-- source:
--   Original Avram BV finitecap capHJB45 obligation and pinned proved boundedVariation_generator_physical_drift_representation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB45_interior_BV_source_HJB_to_derivative_loss_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (ε c W η A : ℝ)
    (hε : 0 < ε) (hεc : ε < c)
    (hwGen : ∀ y ∈ Ioo ε c,
      X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0)
    (hwUpper : ∀ y ∈ Ioo ε c, q * w y ≤ W)
    (hLoss : ∀ b ∈ Ioo ε c,
      ∀ y ∈ Icc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M) :
    ∀ b ∈ Ioo ε c,
      ∀ y ∈ Ioo ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w y ≤ (W + A) + η * M := by sorry
