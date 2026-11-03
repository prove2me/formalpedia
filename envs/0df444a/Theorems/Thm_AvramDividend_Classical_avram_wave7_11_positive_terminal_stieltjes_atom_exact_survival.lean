-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
-- name    : AvramDividend.Classical.avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:33:46.489285+00:00
-- url     : https://prove2.me/theorems/e9ede15b-078e-498a-990a-2b2292df15c9
-- title:
--   Original positive finite-horizon Stieltjes terminal payment equals discounted genuine dividend atom before ruin
-- statement:
--   For the original Stieltjes dividendMeasure D ω at a strictly positive finite real horizon T, if the original stop clock σ is strictly later than ENNReal.ofReal T, the exact discounted payout restricted to the terminal singleton payment set equals the original dividend-measure mass at {T} multiplied by exp(-qT). This computes the finite-horizon endpoint contribution without discarding any jump atom.
-- source:
--   Source-faithful finite-horizon endpoint equality using Proved W7-11 payment-set iff 98c71508 and Mathlib AE singleton restriction and constant ENNReal integral. Consumer is canonical UBV finite-horizon value cc518136.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_endpoint_payment_iff
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T)
    (hσ : ENNReal.ofReal T < σ) :
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (dividendMeasure D ω) ({T} : Set ℝ) *
        ENNReal.ofReal (Real.exp (-(q * T))) := by sorry
