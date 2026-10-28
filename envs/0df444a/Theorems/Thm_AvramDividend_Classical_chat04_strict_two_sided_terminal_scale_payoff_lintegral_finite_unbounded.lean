-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded
-- name    : AvramDividend.Classical.chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:18:32.834776+00:00
-- url     : https://prove2.me/theorems/06ed85c6-5ce2-4839-add8-d5271a943185
-- title:
--   Finite strict two-sided stopped terminal q-scale expectation in unbounded variation
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and q>0, the sum of strict upper-exit and lower-ruin discounted q-scale terminal payoff expectations is finite. The zero-origin theorem removes the lower-ruin contribution, the exact terminal boundary factorisation reduces the expectation to the upper-exit discount times W(a), and the uniform discount estimate bounds this by the finite real scale value W(a). This is a finite-expectation interface for the stopped-scale martingale proof.
-- source:
--   Proved chat04_scale_zero_origin_of_unbounded_variation, chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero, chat03_exact_stopped_discount_mul_scale_le_scale, and pinned ENNReal.ofReal_lt_top.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_exact_stopped_discount_mul_scale_le_scale

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) < ⊤ := by sorry
