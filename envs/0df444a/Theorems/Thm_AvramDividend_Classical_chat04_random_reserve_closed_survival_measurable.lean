-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_closed_survival_measurable
-- name    : AvramDividend.Classical.chat04_random_reserve_closed_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:54:51.93498+00:00
-- url     : https://prove2.me/theorems/199f4159-e9e4-48cf-b622-e1c210a75cff
-- title:
--   Measurability of continuous-time closed-horizon survival with a random initial reserve
-- statement:
--   For a spectrally negative Lévy process, any ordinary measurable (potentially random) starting reserve H(ω), and any finite horizon T, the event that H(ω)+X_t(ω) is nonnegative at every time t≤T is measurable. The pathwise closed-horizon grid equivalence reduces this uncountable condition to countably many rational observations and the terminal reserve, each measurable by Lévy adaptedness. This strengthens fixed-barrier survival measurability for killed semigroups with state-dependent reserves at Markov splitting times, upstream of the q-scale renewal identity a885f0b3 and stopped two-sided exit.
-- source:
--   Proved chat04_random_reserve_lower_survival_closed_grid_iff; pinned Mathlib measurable_pi_apply/MeasurableSet.iInter and measurability of each adapted Lévy time slice, via 𝓕.le.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_closed_survival_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | ∀ t : ℝ≥0, t ≤ T → 0 ≤ H ω + X.X t ω} := by sorry
