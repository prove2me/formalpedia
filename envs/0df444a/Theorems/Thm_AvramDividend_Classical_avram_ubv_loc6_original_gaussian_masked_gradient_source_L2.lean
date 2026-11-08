-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:57:44.871437+00:00
-- url     : https://prove2.me/theorems/7ae1130d-7935-43f5-ad75-a3ce3d5de9ac
-- title:
--   Original masked Gaussian source coefficient predictable with finite quadratic energy
-- statement:
--   For the actual spectrally negative Lévy Gaussian coefficient X.σ multiplied by the derivative of the candidate w at the original physical pre-right-dividend reserve left limit, set to zero outside an interior compact band, prove both measurability on the right-continuous predictable sigma algebra and finite square energy on any finite predictable observation measure. This is for exactly the original X, D and reserve convention, including jumps and time-zero; the existing compact gradient result does not itself supply the X.σ factor.
-- source:
--   Original Proved predictable compact-gradient theorem bcd9edf0 and analytic derivative bound derivative_abs_le_on_compact_interior_interval; bound |X.σ H|≤|X.σ| M on the identical μ and use monotonicity of the lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual Gaussian source X.σ times the masked original pre-payment
    gradient is predictable and has finite square energy on the same finite
    right-continuous predictable measure, without changing sigma algebra. -/

theorem AvramDividend.Classical.avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    Measurable[𝓕.rightCont.predictable] G ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ := by sorry
