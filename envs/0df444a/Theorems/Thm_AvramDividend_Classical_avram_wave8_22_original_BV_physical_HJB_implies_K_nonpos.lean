-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_physical_HJB_implies_K_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_physical_HJB_implies_K_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:18:17.793109+00:00
-- url     : https://prove2.me/theorems/96a0491b-926d-4c63-8808-c5fc0bf9ee6c
-- title:
--   Original Lévy BV local HJB gives nonpositive physical generator on stopped positive region
-- statement:
--   For the original spectrally negative Lévy process, its original physical drift and negative Lévy jump integral yield a nonpositive discounted stopped generator whenever the source HJB inequality holds at positive capital and the actual stopped path stays strictly positive. No surrogate process or martingale centring.
-- source:
--   Avram original BV HJB generator, positive stopped capital, exp nonnegative

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_physical_HJB_implies_K_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (A : Ω → Set ℝ≥0)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (hHJB : ∀ y : ℝ, 0 < y →
    X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0)
  (hPositive : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) :
  ∀ᵐ ω ∂P, ∀ t, t ∈ A ω → K t ω ≤ 0 := by sorry
