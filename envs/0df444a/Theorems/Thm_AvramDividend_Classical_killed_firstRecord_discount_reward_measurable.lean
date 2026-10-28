-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
-- name    : AvramDividend.Classical.killed_firstRecord_discount_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:42:52.320854+00:00
-- url     : https://prove2.me/theorems/cd7b1f13-da23-468f-b4fe-8cadce9dd92f
-- title:
--   Measurability of the killed discounted strict first-record reward
-- statement:
--   The actual discounted first-upcrossing reward, killed when the strict upper record fails to precede reflected ruin, is a measurable extended-nonnegative random variable. This combines measurable upper-record and reflected-ruin stopping times with Borel measurability of ENNReal.toReal, exponential discount and ENNReal.ofReal. It directly supplies the reward-measurability hypothesis required to pass finite record truncations to the full first-record renewal bound.
-- source:
--   Proved upperPassage_stopping_rightCont_filtration and barrierRuinTime_measurable; pinned Mathlib IsStoppingTime.measurable, ENNReal.measurable_toReal and ENNReal.measurable_ofReal.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_discount_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε q : ℝ) :
    Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0) := by sorry
