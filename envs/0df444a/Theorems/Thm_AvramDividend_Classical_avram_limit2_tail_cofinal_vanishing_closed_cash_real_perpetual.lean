-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_tail_cofinal_vanishing_closed_cash_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_tail_cofinal_vanishing_closed_cash_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:41:51.933888+00:00
-- url     : https://prove2.me/theorems/200c5748-2676-41d2-a7ec-74eb7955f1c0
-- title:
--   Original closed nonmonotone tail-cofinal horizon cash with vanishing error controls real perpetual dividend value
-- statement:
--   For the original spectrally negative Levy X and admissible D, every tail of the possibly nonmonotone deterministic real horizon T is cofinal. The expectation of discounted Stieltjes cash on paymentTimes(ruinTime) intersect Iic (T k) plus a nonnegative terminal is bounded by finite B plus asymptotically vanishing ENNReal error. Each standard integer horizon fits inside a sufficiently late T(k) with small error, so by positive additive epsilon removal and the accepted original integer horizon exhaustion, actual dividendValue <= B. The accepted genuine original signed Stieltjes theorem gives integrability and exact real expectation identity, with time-zero/endpoint atoms preserved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_tail_cofinal_vanishing_closed_cash_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ)
    (hTail : ∀ (N : ℕ) (a : ℝ), ∃ k : ℕ, N ≤ k ∧ a ≤ T k)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (T k),
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
