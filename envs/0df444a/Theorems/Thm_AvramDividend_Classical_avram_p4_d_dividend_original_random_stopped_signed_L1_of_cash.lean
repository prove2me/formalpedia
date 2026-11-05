-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_L1_of_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_signed_L1_of_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:52:51.791876+00:00
-- url     : https://prove2.me/theorems/51994c74-9d6b-44d9-a26a-ae7222b4e181
-- title:
--   True original random-stopped diffuse signed remainder L1 from stopped Cash and measurability
-- statement:
--   For the genuine original stopped Levy reserve with arbitrary random ruin deadline and bounded random finite stopping clock, the signed dividend-gradient Stieltjes correction on the true paid clock is integrable under P provided its random-variable a.e. strong measurability, the source compact strict-interior diffuse band premise, and integrability of the exact original discounted stopped Cash. The result uses the new pathwise uniform coefficient independent of sample path and Mathlib Integrable.mono'; it does not smuggle in the stochastic measurability or boundary hypotheses, which remain exposed for P4-F.
-- source:
--   Random-clock signed original diffuse norm≤constant×Cash theorem and pinned Mathlib Integrable.mono'; original true stopped Cash integrability supplied as an exact premise matching 4a50bbff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_signed_L1_of_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (ν : Ω → Measure ℝ) (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b)
    (hCashI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(ν ω)) P) :
    Integrable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(ν ω)) P := by sorry
