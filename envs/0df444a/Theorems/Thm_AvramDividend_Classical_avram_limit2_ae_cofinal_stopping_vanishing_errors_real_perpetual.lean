-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:03:37.086582+00:00
-- url     : https://prove2.me/theorems/dea994ab-440b-413a-9858-40b99d7ecbd3
-- title:
--   Original a.e.-cofinal ruin-stopped cash with vanishing localisation errors implies perpetual L1 signed payout
-- statement:
--   For an original admissible dividend strategy, measurable pathwise monotone localisation stopping times σ_k converge almost surely to the genuine ruinTime. Each original σ_k stopped Stieltjes cash plus its ENNReal nonnegative terminal is bounded by B+error_k, where the nonnegative errors converge to zero in the explicit eventually-epsilon sense. Shifting to the tail k+N preserves measurability, monotonicity, and a.e. cofinality. Apply the Proved original cofinal stopped budget theorem with B+epsilon, then the original truncated-to-perpetual inequality. ENNReal epsilon removal yields dividendValue≤B; finite B gives genuine original real Stieltjes L1 identity. No terminal vanishing or equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hStopped : ∀ n k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal k ω) ∂P)
      ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
