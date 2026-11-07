-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f22_original_all_compact_stopped_terminal_L1_from_reward
-- name    : AvramDividend.Classical.avram_f22_original_all_compact_stopped_terminal_L1_from_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:36:32.539766+00:00
-- url     : https://prove2.me/theorems/d3fa6d88-0550-42fc-accd-74b39306f568
-- title:
--   Every exact original compact stopped reward has integrable terminal component
-- statement:
--   For the original admissible dividend process, any countable family of right-continuous stopping clocks dominated by an integrable-cash reference clock has integrable discounted terminal components as soon as its exact terminal plus closed Stieltjes cash rewards are integrable. All clocks and original ruinTime and inclusive cash measure are preserved. Enables Gaussian and pure-jump Itô-Meyer source verification for arbitrary localisers.
-- source:
--   F7/F53 original arbitrary compact-clock Ito witness terminal-L1 input: theorem applies uniformly k to exact stopped rewards.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_f22_original_all_compact_stopped_terminal_L1_from_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hBound : ∀ k ω, σ k ω ≤ τ ω)
    (Term F : ℕ → Ω → ℝ)
    (hExact : ∀ k ω, F k ω = Term k ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, Integrable (Term k) P := by sorry
