-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB47_original_BV_uniform_near_cap_deriv_of_full_mark_loss
-- name    : AvramDividend.Classical.avram_bva_capHJB47_original_BV_uniform_near_cap_deriv_of_full_mark_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:22.684815+00:00
-- url     : https://prove2.me/theorems/5eaf3a5b-0fa5-4e00-8448-73f916282419
-- title:
--   Source BV interior HJB and full negative-mark loss give uniform derivative bound up to finite cap
-- statement:
--   For original bounded-variation spectrally negative Levy with physical positive drift, actual interior HJB generator upper bound and full negative-jump loss bound by an integrable small first moment times the derivative compact maximum give a uniform derivative bound up to the finite upper cap. Compose the true original generator representation capHJB45 with capHJB44 maximum absorption. This is source-specific analytic input to build true inclusive-cap full jump kernel Lipschitz rather than arbitrary strict spatial masks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB47_original_BV_uniform_near_cap_deriv_of_full_mark_loss
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (ε c W A η B : ℝ)
    (hε : 0 < ε) (hεc : ε < c)
    (hη : η < X.drift)
    (hLocal : ∀ t ∈ Icc (ε / 2) ε, deriv w t ≤ B)
    (hMax : ∀ b ∈ Ioo ε c,
      ∃ s ∈ Icc (ε / 2) b,
        ∀ t ∈ Icc (ε / 2) b, deriv w t ≤ deriv w s)
    (hGen : ∀ y ∈ Ioo ε c,
      X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0)
    (hwUpper : ∀ y ∈ Ioo ε c, q * w y ≤ W)
    (hLoss : ∀ b ∈ Ioo ε c,
      ∀ y ∈ Icc ε b, ∀ M : ℝ,
      (∀ r ∈ Icc (ε / 2) b, deriv w r ≤ M) →
      -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
        A + η * M) :
    ∀ t ∈ Ico (ε / 2) c,
      deriv w t ≤ max B ((W + A) / (X.drift - η)) := by sorry
