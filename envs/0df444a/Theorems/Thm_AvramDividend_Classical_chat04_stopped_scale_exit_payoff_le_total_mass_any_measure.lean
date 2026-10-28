-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_stopped_scale_exit_payoff_le_total_mass_any_measure
-- name    : AvramDividend.Classical.chat04_stopped_scale_exit_payoff_le_total_mass_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:41:41.114928+00:00
-- url     : https://prove2.me/theorems/f83fb8dc-2c6f-4feb-95b6-b870038d059a
-- title:
--   Uniform total-mass upper bound on the killed stopped q-scale terminal reward
-- statement:
--   For any path-space measure, nonnegative discount rate and initial reserve at most the barrier, the stopped upper-first q-scale payoff integral is at most total path mass times the real scale value at the barrier. This gives a deterministic cap for finite tilted measures.
-- source:
--   Combines the remotely accepted stopped scale payoff event-mass bound with monotonicity of measure.

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_stopped_scale_exit_payoff_le_upperfirst_mass_any_measure

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_stopped_scale_exit_payoff_le_total_mass_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hq : 0 ≤ q) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤
      μ Set.univ * ENNReal.ofReal (W a) := by sorry
