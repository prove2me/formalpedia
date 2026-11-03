-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_expected_terminal_atom_zero_if_clock_ended
-- name    : AvramDividend.Classical.avram_wave7_11_expected_terminal_atom_zero_if_clock_ended
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:21:29.034746+00:00
-- url     : https://prove2.me/theorems/9809391e-fcc4-4891-85b5-47c2615f2841
-- title:
--   Original expected terminal Stieltjes payment atom vanishes once all sample clocks have ended
-- statement:
--   For an original random stopping clock σ satisfying σ(ω)≤ENNReal.ofReal T for every original sample ω at a strictly positive real horizon, the expected discounted Stieltjes contribution of the exact terminal singleton paymentTimes(σ ω)∩{T} is zero. All integrals retain the source dividendMeasure D ω and original probability P.
-- source:
--   Probability-expectation corollary of Proved W7-11 no-terminal-payment-if-clock-ended theorem 0e0c52cb; it isolates a clean exact-endpoint branch for canonical UBV value accounting.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_expected_terminal_atom_zero_if_clock_ended
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (T : ℝ) (hT : 0 < T)
    (hσ : ∀ ω, σ ω ≤ ENNReal.ofReal T) (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by sorry
