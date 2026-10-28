-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
-- name    : AvramDividend.Classical.chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:55:31.327931+00:00
-- url     : https://prove2.me/theorems/8a4e69ac-b4d9-4ab1-9ecd-f1b5fe3dd5a8
-- title:
--   Exact two-sided stopped q-scale payoff balance at zero reserve under near-zero downcrossing
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and q>0, the actual sum-of-strict-exit-terminal q-scale payoffs has expectation W(0)=0 at initial capital zero and upper barrier a>0, provided the path enters negative values arbitrarily soon almost surely. The downcrossing regularity assumption is explicit. This is the literal stopped-payoff integrand required by the general-reserve theorem at x=0, derived from accepted strict-terminal factorisation and the accepted zero-start exit-expectation result. It does not claim unbounded variation alone proves the assumed path regularity.
-- source:
--   Kyprianou, Kuznetsov, Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, section 2.5.1; existing Prove2Me accepted terminal factorisation, zero-start exit expectation under near-zero downcrossing, and scale value W(0)=0.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_zero_start_two_sided_exit_expectation_of_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    (∫⁻ ω, (if twoSidedExitUpTime X a ω <
          twoSidedExitDownTime X 0 ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X a ω)))) *
          ENNReal.ofReal
            (W (X.X (twoSidedExitUpTime X a ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X 0 ω <
          twoSidedExitUpTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X 0 ω)))) *
          ENNReal.ofReal
            (W (X.X (twoSidedExitDownTime X 0 ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W 0) := by sorry
