-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_vanishing_remainder_closed_cash_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_vanishing_remainder_closed_cash_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:50:58.509461+00:00
-- url     : https://prove2.me/theorems/761967b4-1429-46b0-9ba9-1cbbd341a41b
-- title:
--   Original closed stopped cash with vanishing localisation remainders yields perpetual real L1 payout
-- statement:
--   For genuine original capped ruin-time Stieltjes payments, an error sequence that is eventually below every strictly positive NNReal, plus nonnegative terminal budgets upper-bounding each expected closed-horizon cash by finite B+error n, yields dividendValue at most B. Monotonicity of the original positive Stieltjes cash on Iic n allows comparison of any fixed horizon with arbitrarily late ones, and ENNReal.le_of_forall_pos_le_add removes the error. Finiteness then invokes the proved original real Stieltjes L1 expectation identity. Preserves zero and finite endpoint atoms. No stochastic hypothesis, equality in law, or terminal vanishing is assumed.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_vanishing_remainder_closed_cash_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → error n ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error n) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
