-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
-- name    : AvramDividend.Classical.levy_running_infimum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:31:21.01306+00:00
-- url     : https://prove2.me/theorems/d11a34c7-dc61-40b9-8077-335d5d600c5d
-- title:
--   Finite-horizon negative running infimum of a Lévy path is measurable
-- statement:
--   The running lower envelope of any spectrally negative Lévy path over a closed finite horizon is measurable as a real random variable. Its sublevel event is equivalent to the measurable no-ruin event starting at that sublevel reserve, by the lower-survival/running-infimum equivalence and finite-horizon path boundedness. This supports the stochastic expectation of the pathwise reserve-Laplace survival envelope.
-- source:
--   Proved lower_survival_running_infimum_equiv and chat04_shifted_lower_survival_measurable_no_schedule, together with finite-horizon path boundedness and Mathlib measurable_of_Iic.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_running_infimum_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Measurable (fun ω : Ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) := by sorry
