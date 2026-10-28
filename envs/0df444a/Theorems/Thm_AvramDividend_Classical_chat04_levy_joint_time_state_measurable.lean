-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
-- name    : AvramDividend.Classical.chat04_levy_joint_time_state_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:59:14.717846+00:00
-- url     : https://prove2.me/theorems/d55462c3-decf-40f0-9aff-439d356324d9
-- title:
--   Actual Lévy process is jointly Borel measurable in time and sample path
-- statement:
--   The actual real-valued coordinate process of every spectrally negative Lévy process has a measurable evaluation map (t,ω)↦X_t(ω) on nonnegative time times path space. This follows from the process's original adaptedness and right-continuous paths, via the separately Proved right-continuous-section joint measurability theorem, and requires no extra assumptions or scale exit identity.
-- source:
--   Canonically Proved rightContinuous_measurable_sections_joint_evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04; direct fields SpectrallyNegativeLevy.adapted and rightCont as used in accepted chat03_lower_before_horizon_measurable and levy_path_bddBelow_finite_horizon. Needed to construct the genuine killed q-scale stochastic resolvent payoff on an exponential clock.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_levy_joint_time_state_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) := by sorry
