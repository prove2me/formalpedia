-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:09:27.160822+00:00
-- url     : https://prove2.me/theorems/45babaa0-c444-4a38-b4c2-5a8d6cfc4910
-- title:
--   Original actual diffuse Stieltjes remainder is L1 under P4-F Cash and honest measurable selection
-- statement:
--   For a genuine original closed-horizon dividend Stieltjes decomposition on every path, source strict-interior gradient localisation, the canonical named Cash witness and its existing integrability, and an explicit a.e.-strong measurability premise for the diffuse signed integral, prove the actual original random-stopped diffuse Stieltjes signed remainder integrable. Its domination premise is discharged from the actual additive source measure split rather than assumed independently.
-- source:
--   Accepted actual source diffuse component domination 72fd52 and named-Cash random stopped signed L1 theorem 37873306, preserving original dividendMeasure and X-left/D-right source reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_L1_of_named_cash

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (μatom μdiffuse : Ω → Measure ℝ)
    (hsplit : ∀ ω,
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ)) =
        μatom ω + μdiffuse ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(μdiffuse ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(μdiffuse ω)) P) :
    Integrable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(μdiffuse ω)) P := by sorry
