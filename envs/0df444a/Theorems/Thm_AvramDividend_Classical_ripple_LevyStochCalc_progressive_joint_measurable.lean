-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_LevyStochCalc_progressive_joint_measurable
-- name    : AvramDividend.Classical.ripple_LevyStochCalc_progressive_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:00:41.51233+00:00
-- url     : https://prove2.me/theorems/26c7a137-ff7e-4d92-abaa-a2730f3a0bb0
-- title:
--   Every genuine LevyStochCalc progressively measurable Brownian integrand is jointly measurable in time and sample
-- statement:
--   For any real-time filtration and original sample space, LevyStochCalc.Probability.ProgressivelyMeasurable Fr H implies ordinary joint measurability of the actual function (omega,t) maps to H omega t. Cover the full real time axis by increasing deterministic finite ceilings and use truncated source strong measurability on each ceiling, promoted through the filtration inclusion to the original full sigma-algebra. The truncated sequence is eventually exactly the original integrand and its pointwise limit is jointly measurable. This discharges the remaining joint-measurability premise of the actual LevyStochCalc Brownian Ito integral.
-- source:
--   Pinned Mathlib stronglyMeasurable_of_tendsto, tendsto_pi_nhds, Filtration.le and LevyStochCalc/Probability/Progressive.lean, imported Definition KLSModular_LevyStochCalc_Probability_Progressive.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.ripple_LevyStochCalc_progressive_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Fr : Filtration ℝ mΩ) (H : Ω → ℝ → ℝ)
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable Fr H) :
    Measurable (Function.uncurry H) := by sorry
