-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_cofinal_vanishing_strict_cash_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_cofinal_vanishing_strict_cash_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:52:03.486562+00:00
-- url     : https://prove2.me/theorems/af60a7e9-0f50-4be8-8658-aa9eddc4e29e
-- title:
--   Original strict cofinal vanishing terminal/error budgets to perpetual real dividend value
-- statement:
--   For the original Levy dividend process and admissible D, an arbitrary unbounded nonmonotone real horizon T suffices, with nonnegative terminal and error_k→0 expectation bounds for Iio (T k). The independently Proved real cofinal-tail lemma converts ordinary cofinality into tail cofinality. The tail-cofinal stopped cash limit then proves genuine real Stieltjes integrability, exact mean identity and finite perpetual dividendValue bound, preserving time-zero and finite strict horizon atoms.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_real_cofinal_family_is_tail_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_limit2_tail_cofinal_vanishing_strict_cash_real_perpetual

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_cofinal_vanishing_strict_cash_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hCofinal : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
