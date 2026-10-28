-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_future_extracted_poisson_marked_compensation_ws01b
-- name    : AvramDividend.Classical.bv_actual_levy_future_extracted_poisson_marked_compensation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:33:33.372993+00:00
-- url     : https://prove2.me/theorems/be6507c5-b60c-4576-ab3a-88fc8f1fd303
-- title:
--   Actual Lévy future-jump predictable compensation from a measurable Poisson path extractor and its law
-- statement:
--   For a source spectrally negative Lévy process, let a measurable functional of its actual shifted future increment path supply an ordered count K and sequence of jump marks Y with a Poisson count law, common integrable mark law and count/mark independence. Then for every integrable F_s-measurable reserve-dependent weight H and mark test f, the actual source expectation of H times the future marked sum equals the past mean times the Poisson rate times the mark mean. Crucially, past–future independence is *proved* from the source Lévy property, not additionally assumed. Establishing that the source's large-jump extractor actually has the stated Poisson law is the remaining substantive probabilistic bridge.
-- source:
--   Derives the source past/future independence from the canonically Proved full Lévy future path product law and uses Proved closed marked-Poisson compensation. Avoids private LeanLevy imports and does not assume generator-to-Dynkin or killed semigroup identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.bv_actual_levy_future_extracted_poisson_marked_compensation_ws01b
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (hHi : Integrable H P)
    (J : (ℝ≥0 → ℝ) → (ℕ × (ℕ → E))) (hJ : Measurable J)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
        (K ω, fun n : ℕ => Y n ω))
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hYm : ∀ n, Measurable (Y n))
    (ν : Measure E) (hYL : ∀ n, HasLaw (Y n) ν P)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) P)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    (∫ ω, H ω * (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂P) =
      (∫ ω, H ω ∂P) * ((r : ℝ) * ∫ y, f y ∂ν) := by sorry
