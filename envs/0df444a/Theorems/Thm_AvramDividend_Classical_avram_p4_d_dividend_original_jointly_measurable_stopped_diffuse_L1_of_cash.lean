-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_jointly_measurable_stopped_diffuse_L1_of_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_jointly_measurable_stopped_diffuse_L1_of_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:01:04.671511+00:00
-- url     : https://prove2.me/theorems/b79313f3-ac6b-4f74-9b58-1e5f72ac4664
-- title:
--   Joint original stopped dividend-gradient measurability and named Cash imply integrable signed Stieltjes remainder
-- statement:
--   Given the true closed original Stieltjes split with a measurable s-finite diffuse subkernel, strict-interior compact reserve control, and the exact named discounted Cash L1 witness, the actual signed diffuse discounted dividend-gradient integral is integrable. The usual independent a.e. integral-selector measurability premise is replaced by the source-exact joint strong measurability of the stopped integrand and its pathwise Borel payment window, which are inputs to the proved s-finite kernel integration theorem.
-- source:
--   Accepted original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash 45babaa0 and source-specific stopped integral-kernel strong measurability bridge ee23eb2b, using its AEStronglyMeasurable consequence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_jointly_measurable_stopped_diffuse_L1_of_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (μatom : Ω → Measure ℝ) (κdiff : Kernel Ω ℝ)
    [IsSFiniteKernel κdiff]
    (hsplit : ∀ ω,
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ)) =
        μatom ω + κdiff ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(κdiff ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hWindow : ∀ ω, MeasurableSet
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)))
    (hJoint : StronglyMeasurable (fun p : Ω × ℝ =>
      (paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)).indicator
        (fun s : ℝ => Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r p.1) s.toNNReal -
            rightLimit D s.toNNReal p.1))) p.2)) :
    Integrable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) P := by sorry
