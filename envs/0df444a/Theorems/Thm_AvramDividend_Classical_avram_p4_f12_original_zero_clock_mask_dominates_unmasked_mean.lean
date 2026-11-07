-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
-- name    : AvramDividend.Classical.avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:12:50.899845+00:00
-- url     : https://prove2.me/theorems/3e8ea98a-bb0a-4c41-bd17-680a6beef10f
-- title:
--   Original stopped-reward zero-clock mask increases expected reward
-- statement:
--   At the exact original stopping clock, the zero-time dividend-jump constraint implies the physical payoff F is at most w(x) whenever the clock is zero. Thus replacing F there by w(x) weakly increases the expected reward. This explicitly rules out inferring the required masked budget from an unmasked budget.
-- source:
--   Original physical dividend process and proved zero-clock payoff inequality; Bochner integral monotonicity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hzero_meas : ∀ k, MeasurableSet {ω : Ω | σ k ω = 0}) :
    ∀ k, (∫ ω, F k ω ∂P) ≤
      ∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P := by sorry
