-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_stopped_scale_exit_payoff_ne_top_finite_measure
-- name    : AvramDividend.Classical.chat04_stopped_scale_exit_payoff_ne_top_finite_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:39:15.352851+00:00
-- url     : https://prove2.me/theorems/29ecd8eb-92e4-4101-84bd-d9f8b7abc761
-- title:
--   Stopped strict upper-exit q-scale payoff lower integral is finite under any finite law
-- statement:
--   For nonnegative discount and a finite measure on the path space, the strict stopped upper-first terminal q-scale payoff has finite lower integral, since upper exit gives the finite real barrier scale value.
-- source:
--   Combines remotely accepted arbitrary-measure stopped payoff factorisation with the finite-mass upper-first discounted integral theorem and pinned ENNReal operations.

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.ENNReal.Operations
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_lintegral_ne_top_finite_measure

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_stopped_scale_exit_payoff_ne_top_finite_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (q a x : ℝ) (hq : 0 ≤ q) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≠ ⊤ := by sorry
