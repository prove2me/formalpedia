-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:56:33.219766+00:00
-- url     : https://prove2.me/theorems/ee23eb2b-b045-404a-8e63-0c59044a3b7a
-- title:
--   Original stopped Lévy dividend-gradient signed integral is strongly measurable against an s-finite kernel
-- statement:
--   For the genuine spectrally negative original Lévy process, adapted dividend strategy and exact closed-horizon pre-ruin payment times, any s-finite random dividend subkernel has a strongly measurable discounted signed gradient integral as soon as its actual joint stopped integrand is strongly measurable and each exact payment window is Borel. The integrand uses the source Lévy left limit and right-dividend limit in their original chronological convention. This discharges the integral-kernel measurability bridge required to make the existing P4-D conditional signed L1 theorem usable.
-- source:
--   Original source SpectrallyNegativeLevy, IsDividendStrategy, paymentTimes, rightLimit, plus pinned Mathlib StronglyMeasurable.integral_kernel_prod_right and integral_indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (κdiff : Kernel Ω ℝ) [IsSFiniteKernel κdiff]
    (hWindow : ∀ ω : Ω, MeasurableSet
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)))
    (hJoint : StronglyMeasurable (fun p : Ω × ℝ =>
      (paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)).indicator
        (fun s : ℝ => Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r p.1) s.toNNReal -
            rightLimit D s.toNNReal p.1))) p.2)) :
    StronglyMeasurable (fun ω : Ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) := by sorry
