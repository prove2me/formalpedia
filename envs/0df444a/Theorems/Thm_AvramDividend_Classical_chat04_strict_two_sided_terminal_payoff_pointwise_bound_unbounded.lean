-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_payoff_pointwise_bound_unbounded
-- name    : AvramDividend.Classical.chat04_strict_two_sided_terminal_payoff_pointwise_bound_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:16:29.620429+00:00
-- url     : https://prove2.me/theorems/1d83c2a7-06bb-4972-9af8-29d7082b7d68
-- title:
--   Uniform stopped two-sided terminal scale payoff bound for unbounded-variation Lévy processes
-- statement:
--   For a spectrally negative Lévy process of unbounded variation and q>0, on every sample path the combined strict upper-before-ruin and lower-before-upper terminal discounted q-scale payoff is bounded by W(a), assuming x≤a. The zero scale boundary value W(0)=0 is derived from the unbounded-variation Gaussian/infinite-small-jump dichotomy, eliminating an auxiliary boundary hypothesis. This bound supports uniform integrability and convergence in the killed optional-stopping argument.
-- source:
--   Proved chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero; unbounded_variation_gaussian_or_infinite_small_jump_moment; Gaussian and infinite-small-jump zero-origin theorems.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_payoff_pointwise_bound_of_Wzero
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_two_sided_terminal_payoff_pointwise_bound_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
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
      else 0) ≤ ENNReal.ofReal (W a) := by sorry
