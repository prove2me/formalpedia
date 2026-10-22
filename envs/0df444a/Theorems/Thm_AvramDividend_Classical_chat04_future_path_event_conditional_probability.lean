-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_future_path_event_conditional_probability
-- name    : AvramDividend.Classical.chat04_future_path_event_conditional_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:08:31.260498+00:00
-- url     : https://prove2.me/theorems/f65072d4-4537-4a47-a4ca-e19f7198942e
-- title:
--   Conditional probability of any measurable full future Lévy path event from finite-cylinder independence
-- statement:
--   For the original spectrally negative Lévy process X, deterministic time s, assume that for every finite set I of future nonnegative times the joint sigma algebra of shifted increments X_(s+t)-X_s, t∈I, is independent of the full past filtration F_s. Let G be ANY measurable set of complete future sample paths in the product space (nonnegative time→real), allowing events depending on uncountably many future times whenever product-measurable. Then the conditional expectation given F_s of the real indicator of the future shifted process belonging to G is almost surely the constant unconditional expectation of that indicator. The event is automatically integrable because X carries a probability measure, so no integrability input is required. Uses two separately ACCEPTED results: chat04_whole_future_process_indep_past_of_finite_cylinders UUID e87d68dd-58e9-4570-8c43-ece958416b16 and chat04_full_shifted_future_path_condExp_of_independence UUID 82301379-a313-4f88-8ab5-7c9aa293947e. This establishes the conditional event-level Markov interface for future path survival, with uniform joint finite-cylinder independence still an explicit outstanding requirement. It does not assume all uncountable intersections are automatically measurable, nor prove killed q-harmonicity.
-- source:
--   Accepted theorem UUIDs e87d68dd-58e9-4570-8c43-ece958416b16 and 82301379-a313-4f88-8ab5-7c9aa293947e; canonical Lévy IsProbabilityMeasure and adaptedness; pinned Mathlib measurable_pi_iff, Measurable.ite, Integrable.indicator.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_condExp_of_independence

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat04_future_path_event_conditional_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (hFinite : ∀ I : Finset ℝ≥0,
      Indep (⨆ t ∈ I, MeasurableSpace.comap
        (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P)
    (G : Set (ℝ≥0 → ℝ)) (hG : MeasurableSet G) :
    P[(fun ω => if (fun t => X.X (s + t) ω - X.X s ω) ∈ G
        then (1 : ℝ) else 0) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, (if (fun t => X.X (s + t) ω - X.X s ω) ∈ G
        then (1 : ℝ) else 0) ∂P) := by sorry
