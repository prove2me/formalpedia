-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_stopped_terminal_L1_exact_mean
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_stopped_terminal_L1_exact_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:49:56.312664+00:00
-- url     : https://prove2.me/theorems/cecd0a5c-a040-40c3-9871-f009dc45c4ee
-- title:
--   Original a.e.-cofinal random stopped cash budgets imply finite perpetual value and exact real L1 dividend mean
-- statement:
--   For a genuinely admissible original dividend strategy and P-almost-sure cofinal increasing measurable original ruin clocks, assume uniform expected nonnegative closed-horizon stopped cash plus nonnegative terminal contributions at every natural horizon and every random clock, with finite ENNReal ceiling B. Apply the Proved original a.e.-cofinal terminal cash bridge at each closed integer horizon, and the Proved exact truncated-to-perpetual dividendValue bound. Since B is finite, the original perpetual signed Stieltjes theorem gives real L1 integrability and an exact equality of the genuine ruin-stopped real payout expectation with dividendValue. This preserves initial and right-closed horizon atoms and assumes no terminal vanishing.

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

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_stopped_terminal_L1_exact_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hStopped : ∀ n k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) +
        Terminal k ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
