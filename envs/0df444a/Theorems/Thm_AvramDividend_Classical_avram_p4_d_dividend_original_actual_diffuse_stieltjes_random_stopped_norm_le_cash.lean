-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_norm_le_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_norm_le_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:08:14.41238+00:00
-- url     : https://prove2.me/theorems/a026711d-ff98-4648-afd2-e516ac907f8f
-- title:
--   Actual original diffuse Stieltjes component uniformly norm-bounded by stopped Cash under source interior band
-- statement:
--   For each sample path assume the actual right-continuous dividend Stieltjes measure on the closed observation interval splits into an atomic and diffuse component, together with a genuine fixed strict-interior reserve band for the source X-left and D-right state. The diffuse component is automatically dominated by the full original dividend measure; applying the accepted random stopped norm theorem gives one deterministic K and a pathwise norm bound by (1+K)exp(qn) times actual stopped Cash. No stochastic measurability of the component selector is invented.
-- source:
--   Accepted original_closed_stieltjes_diffuse_submeasure_actual_dividend 72fd52 and original_random_stopped_signed_norm_le_uniform_cash 80cd452d combined on the actual per-path additive split.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_norm_le_cash
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
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      ‖∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(μdiffuse ω)‖ ≤
        (1 + K) * Real.exp (q * (n : ℝ)) *
          (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
