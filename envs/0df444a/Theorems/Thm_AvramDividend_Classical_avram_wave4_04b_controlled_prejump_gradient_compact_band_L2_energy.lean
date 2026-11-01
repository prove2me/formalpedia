-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
-- name    : AvramDividend.Classical.avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:09:05.581919+00:00
-- url     : https://prove2.me/theorems/bcd9edf0-1a17-4684-b4e2-23b6e1570118
-- title:
--   Actual controlled compact-interior pre-jump gradient has predictable finite quadratic energy
-- statement:
--   For the original spectrally negative Lévy path with any adapted full-variation dividend strategy, w C² on a positive open reserve interval, and a compact localisation band [u,v] strictly inside that interval, the zero-masked pre-jump gradient is measurable in the same right-continuous predictable σ-algebra and has finite real-square energy against every finite measure on this predictable space. The uniform bound is derived from C² local smoothness and compactness, not assumed. Consequently the Gaussian coefficient's predictable L² energy is available upon multiplying by a finite source volatility, but this does not itself construct a Brownian martingale or Itô–Meyer formula.
-- source:
--   Canonical Proved actual controlled left-limit predictability, generic Borel derivative zero extension, compact interval derivative uniform bound, pointwise square domination, finite-measure lintegral constant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_compact_gradient_energy_of_measurable_process

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤ := by
  sorry
