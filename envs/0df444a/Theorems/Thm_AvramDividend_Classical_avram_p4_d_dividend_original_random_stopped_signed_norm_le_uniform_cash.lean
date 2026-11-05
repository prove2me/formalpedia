-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:49:00.057524+00:00
-- url     : https://prove2.me/theorems/80cd452d-7279-41c9-846d-6baa2c5a9102
-- title:
--   Original random-stopped diffuse signed dividend remainder uniformly bounded by literal Cash
-- statement:
--   For the original source Lévy reserve, dividend control D and any random ruin deadline σ(ω), stopped time τ(ω)≤n, and path-dependent dividend submeasure νω dominated by the original Stieltjes measure, suppose the actual source left-X/right-D state lies νω-almost everywhere in a fixed compact strict-interior band. Then there is one deterministic K≥0 independent of ω such that the norm of the genuine signed discounted dividend-gradient Stieltjes integral is at most (1+K) exp(qn) times the literal original stopped Cash.toReal, pathwise for every ω. This gives the uniform integrability envelope P4-F needs under separate source cash L1 and strong measurability.
-- source:
--   Source original C2 interior bound 8e186779, true rightLimit finite Stieltjes mass, random-clock uniform kernel, random-clock mass-to-Cash helper and Mathlib norm_setIntegral_le_of_norm_le_const_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (ν : Ω → Measure ℝ)
    (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      ‖∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(ν ω)‖ ≤
        (1 + K) * Real.exp (q * (n : ℝ)) *
          (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
