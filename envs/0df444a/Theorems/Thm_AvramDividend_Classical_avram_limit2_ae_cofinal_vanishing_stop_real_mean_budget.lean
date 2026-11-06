-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_vanishing_stop_real_mean_budget
-- name    : AvramDividend.Classical.avram_limit2_ae_cofinal_vanishing_stop_real_mean_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:24:00.498971+00:00
-- url     : https://prove2.me/theorems/d2484563-0727-4b66-a801-7bb08694f21b
-- title:
--   Original a.e.-cofinal stopped dividend cash plus vanishing error controls real perpetual payout
-- statement:
--   An original admissible dividend process with measurable monotone a.e.-cofinal stopping clocks to true ruinTime, nonnegative ENNReal terminal witnesses, and vanishing clock-indexed errors has exact real perpetual Stieltjes integrability and expected cash ≤B for each finite nonnegative real B under the original stopped cash+terminal budgets. The accepted source-exact vanishing-error bridge gives full dividendValue≤ENNReal.ofReal B and real L1 exactness; the Proved original real mean comparison gives expected real cash≤B. No terminal vanishing, equality-in-law or modified horizon atoms.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ae_cofinal_stopping_vanishing_errors_real_perpetual
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ae_cofinal_vanishing_stop_real_mean_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ) (hB : 0 ≤ B)
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
      ≤ ENNReal.ofReal B + error k) :
    dividendValue X q x D ≤ ENNReal.ofReal B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
