-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45_left_endpoint_BV_derivative_loss_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB45_left_endpoint_BV_derivative_loss_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T11:21:44.728959+00:00
-- url     : https://prove2.me/theorems/e1492895-f83b-4368-9135-68036668cc9a
-- title:
--   BV generator derivative-loss bound at the lower interior-band endpoint
-- statement:
--   Boundary derivative-loss comparison at y=ε under the full original capHJB45 hypotheses. This is the remaining endpoint obligation after the proved strict-in-ε result capHJB45s; the interior and upper endpoint y>ε follow from capHJB45s. In the absence of continuity of deriv w at ε, the boundary must be established independently.
-- source:
--   Reduction of original capHJB45 to the sole y=ε boundary; reuse proved capHJB45s interval Ioc source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB45_left_endpoint_BV_derivative_loss_envelope
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
      ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w ε ≤ (W + A) + η * M := by sorry
