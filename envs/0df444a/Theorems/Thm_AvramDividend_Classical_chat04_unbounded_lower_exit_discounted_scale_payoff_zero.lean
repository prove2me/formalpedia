-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_lower_exit_discounted_scale_payoff_zero
-- name    : AvramDividend.Classical.chat04_unbounded_lower_exit_discounted_scale_payoff_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:15:52.43498+00:00
-- url     : https://prove2.me/theorems/b697fb05-7d2b-4dda-9311-2be030a7d228
-- title:
--   The lower-first stopped q-scale payoff vanishes under unbounded variation
-- statement:
--   For a spectrally negative Lévy process of unbounded variation and its q-scale function, the nonnegative expectation of the strictly lower-first discounted stopped q-scale payoff is zero, for any upper and initial reserves. The q-scale function vanishes at zero under unbounded variation and its lower-first payoff can contribute only at zero. Thus the entire lower-exit terminal term disappears without imposing a separate no-creeping hypothesis or any optional-stopping identity.
-- source:
--   Previously Proved AvramDividend.Classical.chat04_scale_zero_origin_of_unbounded_variation c1b8958a-41fd-444e-893e-cf03e591b93e and chat04_lower_exit_lintegral_zero_of_Wzero f2638d8a-3194-425a-a9d3-0236eec32af1.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_lower_exit_discounted_scale_payoff_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by sorry
