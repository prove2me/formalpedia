-- Prove2me | Theorems.Thm_AvramDividend_Classical_corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
-- name    : AvramDividend.Classical.corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:58:05.48715+00:00
-- url     : https://prove2.me/theorems/a6c342e4-3362-4673-a43d-df3f1b711236
-- title:
--   Killed upper-first discounted exit is dominated by unrestricted finite-upcrossing discount
-- statement:
--   The q-discounted two-sided upper-before-downcrossing ENNReal expectation is at most the same positive discounted payoff restricted only to the event that the upward first passage time is finite. If τ_up < τ_down, then τ_up<∞, and the two integrands agree. Otherwise the killed integrand is zero and the upper-only integrand is nonnegative. Apply pointwise monotonicity of the Lebesgue lintegral. This elementary but exact stopped-payoff comparison eliminates the lower barrier from the remaining exponential-martingale bound for the unbounded Esscher branch, without relying on any Open theorem.
-- source:
--   Native twoSidedExitExpectationCorrected and ENNReal lintegral_mono

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) :
    twoSidedExitExpectationCorrected X q a x ≤
      ∫⁻ ω, if twoSidedExitUpTimeCorrected X (a - x) ω < (⊤ : ℝ≥0∞)
        then ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTimeCorrected X (a - x) ω))))
        else 0 ∂P := by sorry
