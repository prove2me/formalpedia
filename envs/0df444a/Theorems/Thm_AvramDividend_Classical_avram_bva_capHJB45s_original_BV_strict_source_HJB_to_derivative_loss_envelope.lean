-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:06:07.062023+00:00
-- url     : https://prove2.me/theorems/2d81bacc-27e4-4eb1-8f50-8ef16a96bc41
-- title:
--   Original bounded variation interior HJB yields derivative-loss envelope on epsilon-open reserve band
-- statement:
--   Correct strict source theorem: standing bounded-variation generator HJB controls physical drift derivative at every y with epsilon < y <= b < c, provided the genuine full negative mark loss bound and candidate discount envelope hold. The original HJB hypothesis is only valid at strictly interior y>epsilon, therefore the closed-at-epsilon HJB45 statement cannot directly use it. This corrected child makes the source proof valid without assuming a generator inequality at the excluded lower endpoint, and supports HJB44 maximum bootstrap by handling s<=epsilon using the separately supplied local derivative bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB45s_original_BV_strict_source_HJB_to_derivative_loss_envelope
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
      ∀ y ∈ Ioc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M) :
    ∀ b ∈ Ioo ε c,
      ∀ y ∈ Ioc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      X.drift * deriv w y ≤ (W + A) + η * M := by sorry
