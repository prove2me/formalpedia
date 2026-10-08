-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_indep
-- name    : AvramDividend.Classical.levy_compensated_future_increment_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:22:54.483976+00:00
-- url     : https://prove2.me/theorems/70869717-e9d6-4457-8ff4-c02364768af6
-- title:
--   Compensated exponential of a future Lévy increment is independent of past information
-- statement:
--   For any s≤t and real θ, the compensated exponential of the future increment X_t−X_s is independent of the information filtration at time s. The result follows from the model's Indep of future increments and the fact that σ(exp(θ⋅−(t−s)ψθ)∘increment) is a sub-σ-algebra of σ(increment), since the exponential transform is measurable.
-- source:
--   Direct deterministic measurable-transform consequence of SpectrallyNegativeLevy.indepIncrements; uses Mathlib Probability.Independence.Basic indep_of_indep_of_le_left and MeasurableSpace.comap_comp/comap_mono. A prerequisite for the conditional-expectation proof of the compensated exponential Lévy martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_future_increment_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) :
    Indep
      (MeasurableSpace.comap
        (fun ω => Real.exp
          (θ * (X.X t ω - X.X s ω) -
            ((t - s : ℝ≥0) : ℝ) * X.ψ θ)) inferInstance)
      (𝓕 s) P := by sorry
