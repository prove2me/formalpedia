-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45_original_BV_source_HJB_to_derivative_loss_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB45_original_BV_source_HJB_to_derivative_loss_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:27:51.132088+00:00
-- url     : https://prove2.me/theorems/21aa0954-3684-44ce-953e-83e041651be9
-- title:
--   Original BV full generator HJB implies derivative loss envelope for near-cap bootstrap
-- statement:
--   For the original bounded variation spectrally negative Levy generator, interior supersolution inequality and an upper bound on the discount-weighted candidate, together with a quantitative bound for the full negative-jump loss by large-mark finite cost plus small first moment times the local derivative maximum, imply a physical-drift derivative upper bound. This is the exact source HJB inequality needed by the compact-maximum absorption theorem capHJB44. No spatial exclusion at finite dividend cap and no global generator L1 assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB45_original_BV_source_HJB_to_derivative_loss_envelope
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
      ∀ y ∈ Icc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w y ≤ (W + A) + η * M := by sorry
