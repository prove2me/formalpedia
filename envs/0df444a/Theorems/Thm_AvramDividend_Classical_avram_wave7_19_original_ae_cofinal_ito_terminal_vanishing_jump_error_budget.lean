-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_ito_terminal_vanishing_jump_error_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_ito_terminal_vanishing_jump_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:21:32.087301+00:00
-- url     : https://prove2.me/theorems/af1a0e44-7541-462e-8919-829ca76d49dd
-- title:
--   Original a.s.-cofinal stopped Ito with nonnegative terminal and arbitrarily small jump errors gives full ruin cash budget
-- statement:
--   Under unchanged original-source Lévy/dividend hypotheses and measurable monotone clocks exhausting ruin almost surely, suppose every positive NNReal jump tolerance permits a source stopped Itô–Meyer bound on discounted Stieltjes cash plus its nonnegative terminal payoff, with at most the tolerance added to a finite budget. ENNReal order completeness removes each positive error, the nonnegative terminal is discarded, and the exact source a.s.-cofinal cash bridge yields the full finite-horizon ruin cash expectation inequality. Handles original time-zero dividend atom and excludes positive ruin-time right payment; no uniform integrability or continuity at overshoot.
-- source:
--   Source-specific W7-19 a.s. cofinal cash expectation bridge f96b1f8a-2579-483d-811c-7cc626d89912, random-clock measurability f2bd15ce-a7f8-404d-a706-f94293b9fda3, ENNReal.le_of_forall_pos_le_add; explicitly applies to source jump-truncation plus terminal martingale controls.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_ito_terminal_vanishing_jump_error_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ (k : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal ε k ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
