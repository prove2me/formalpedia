-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB46_original_BV_full_negative_mark_loss_integral_le_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB46_original_BV_full_negative_mark_loss_integral_le_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:19.780181+00:00
-- url     : https://prove2.me/theorems/a71d8db5-0cb4-4f82-9a60-414087d87c84
-- title:
--   Original BV full negative-jump generator loss bounded by the integrable small-big cap mark envelope
-- statement:
--   For actual bounded-variation spectrally negative Lévy source and candidate with finite upper cap, use the original full negative jump kernel integrability from GeneratorIntegrable and BV, the source small-negative-mark Lipschitz/large mark bound and first-jump-moment envelope integrability to dominate the negative full nonlinear generator Lévy jump integral by the integrable source envelope. This provides the quantitative source loss estimate for the near-cap C1 derivative bootstrap; unlike A22 it includes jumps with pre-reserve exactly at finite cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB46_original_BV_full_negative_mark_loss_integral_le_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (c ε L M K : ℝ)
    (hε : 0 < ε) (hεc : ε ≤ c) (hε2 : ε ≤ 2)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * M ≤ K * (ε / 2))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hBound : ∀ r ∈ Icc (0 : ℝ) c, |w r| ≤ M)
    (hLip : ∀ a ∈ Icc (ε / 2) c, ∀ b ∈ Icc (ε / 2) c,
      |w a - w b| ≤ L * |a - b|)
    (y : ℝ) (hy : y ∈ Icc ε c)
    (hGen : X.GeneratorIntegrable w y) :
    -(∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) ≤
      ∫ z in Iio (0 : ℝ),
        (if -(ε / 2) ≤ z then L * |z| else 2 * M) ∂X.ν := by sorry
