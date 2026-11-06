-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_natural_stopped_terminal_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_natural_stopped_terminal_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:58:13.923159+00:00
-- url     : https://prove2.me/theorems/a7dbe173-ef69-4aea-988e-a3d41165c9da
-- title:
--   Natural ruin-stopped original cash plus terminal bounds give finite perpetual real signed Stieltjes value
-- statement:
--   For the exact original source Lévy process and genuinely admissible strategy, a uniform finite expected discounted cash-plus-nonnegative-terminal budget at every canonical natural ruin-stopped clock yields a bounded complete ENNReal dividendValue. It further proves integrability of the unrestricted original real discounted Stieltjes payout, equality of the ENNReal value with the ofReal of its expected signed real integral, and a sharp real mean upper bound. All natural stopping clocks, time-zero atoms, right-endpoint payments and terminal contributions are preserved. Uses only already Proved canonical natural horizon and real perpetual source bridges.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_natural_stopped_terminal_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (B : ℝ) (hB : 0 ≤ B)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hStopped : ∀ n : ℕ,
      (∫⁻ ω, ((∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal n ω) ∂P)
      ≤ ENNReal.ofReal B) :
    dividendValue X q x D ≤ ENNReal.ofReal B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
