-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_condExp_one
-- name    : AvramDividend.Classical.levy_compensated_future_increment_condExp_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:23:36.775837+00:00
-- url     : https://prove2.me/theorems/045f8178-65ec-42ff-ab28-2977ddfdf2de
-- title:
--   Conditional expectation of normalised future Lévy exponential given the past equals one
-- statement:
--   For θ≥0 and s≤t, the compensated exponential future Lévy increment has conditional expectation one given past information 𝓕_s. Its generated sigma-algebra is independent of 𝓕_s, and it has expectation one, while the model's adaptedness supplies ambient measurability. Apply Mathlib condExp_indep_eq using generated sigma-algebra and 𝓕_s, and the process probability measure for sigma-finiteness.
-- source:
--   The two named compensated future increment children and MeasureTheory.condExp_indep_eq in pinned Mathlib revision; prerequisite for the exponential Lévy martingale and generator-to-martingale reasoning.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_future_increment_condExp_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    P[(fun ω => Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ)) | 𝓕 s]
      =ᵐ[P] (fun _ => (1 : ℝ)) := by sorry
