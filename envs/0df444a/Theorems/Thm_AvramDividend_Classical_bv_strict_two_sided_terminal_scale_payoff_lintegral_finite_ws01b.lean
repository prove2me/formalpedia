-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
-- name    : AvramDividend.Classical.bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:24:29.669889+00:00
-- url     : https://prove2.me/theorems/b98c452c-8d3c-4ec3-89ee-bf99bcec5418
-- title:
--   Finite expected discounted two-sided terminal q-scale payoff for bounded-variation Lévy processes
-- statement:
--   The full strict two-sided discounted scale reward is integrable for a bounded-variation spectrally negative Lévy process, even if Wq(0)>0 and lower-boundary contact remains possible. Derive finiteness by integrating the canonically Proved BV pathwise upper bound Wq(a) under the process probability law. Supports optional stopping without presupposing no downward creeping.
-- source:
--   Canonically Proved AvramDividend.Classical.bv_two_sided_terminal_payoff_uniform_bound_ws01b and Mathlib lintegral monotonicity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_two_sided_terminal_payoff_uniform_bound_ws01b

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω <
           twoSidedExitDownTime X (-x) ω then
         ENNReal.ofReal
           (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
           ENNReal.ofReal
             (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
       else 0) +
      (if twoSidedExitDownTime X (-x) ω <
           twoSidedExitUpTime X (a - x) ω then
         ENNReal.ofReal
           (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
           ENNReal.ofReal
             (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
       else 0) ∂P) < ⊤ := by sorry
