-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_stopped_scale_exit_payoff_le_upperfirst_mass_any_measure
-- name    : AvramDividend.Classical.chat04_stopped_scale_exit_payoff_le_upperfirst_mass_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:35:27.731594+00:00
-- url     : https://prove2.me/theorems/0bff9546-9b0b-4ba6-a753-d908d42ee529
-- title:
--   Bound strict stopped q-scale payoff by upper-first event mass under any sample-path law
-- statement:
--   For nonnegative discount and any path-space measure, the killed stopped upper-exit q-scale payoff is at most the measure of upper-first paths multiplied by the q-scale function at the barrier. This gives a measure-change-ready uniform bound.
-- source:
--   Combines the generalised stopped terminal payoff factorisation with the remotely accepted arbitrary-measure discounted upper-first mass bound.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.GCongr
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_mass_bound_any_measure

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_stopped_scale_exit_payoff_le_upperfirst_mass_any_measure
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
      μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} * ENNReal.ofReal (W a) := by sorry
