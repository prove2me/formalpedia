-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_ito_terminal_vanishing_error_full_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_overshooting_ito_terminal_vanishing_error_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:34:22.024305+00:00
-- url     : https://prove2.me/theorems/d3e83091-8270-4e4b-aa36-67508b48767c
-- title:
--   Original overshooting nonmonotone stopped Ito with nonnegative terminal and vanishing jump error yields full ruin cash
-- statement:
--   This is the complete boundary/limit interface for positive-reserve W7-08 when W7-18 supplies measurable possibly nonmonotone stopping clocks with P-a.s. liminf at least the original ruinTime. Each stopped Itô–Meyer inequality may retain an arbitrary nonnegative terminal payoff and an NNReal jump-truncation error ε>0. ENNReal.le_of_forall_pos_le_add removes the error, nonnegativity removes the terminal, and the exact original W7-19 overshooting-ruin cash limit transfers the bound to full finite-horizon discounted dividendMeasure cash. It preserves t=0 right dividend, excludes t=ruin>0 atom, and needs no UI, source-process continuity or stronger canonical hypotheses. The actual stopped stochastic inequality and clock lower-limit coverage remain honest explicit premises.
-- source:
--   W7-19 original overshooting nonmonotone limit theorem 4674e172-bb5c-47d5-a184-fc2de53f3105 when Proved; canonical source terminal positivity and ENNReal jump-tolerance removal as in accepted 3016d001-4947-4fb1-a07a-bca62c91b234.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_overshooting_ito_terminal_vanishing_error_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminfLower : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ (n : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal ε n ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
