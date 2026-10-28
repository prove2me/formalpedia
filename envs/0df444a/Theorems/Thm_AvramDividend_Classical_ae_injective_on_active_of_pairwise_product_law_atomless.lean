-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_injective_on_active_of_pairwise_product_law_atomless
-- name    : AvramDividend.Classical.ae_injective_on_active_of_pairwise_product_law_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:34:13.845493+00:00
-- url     : https://prove2.me/theorems/f833ad3c-78e8-4414-9060-f5660d748d51
-- title:
--   Canonical Poisson marks are collision free on positive-intensity active pieces without requiring dummy zero-mass marks to be diffuse
-- statement:
--   For countably indexed random real arrival times, fix any deterministic predicate active on the index set. Assume pairwise product joint laws and diffuse one-time marginals only on active indices; make no assumptions about the inactive placeholders. Then almost surely the time map is injective on the active set. Restrict the index type to the subtype of active indices, and apply the accepted global countable injectivity theorem to that subtype. This is exactly the correction needed for the canonical LeanLevy Poisson point family: positive-mass partition pieces have atomless time marginals, while zero-mass pieces may have dummy Dirac point distributions. Their counts must be separately proved zero, so the active set is taken to contain only positive-mass piece mark coordinates.
-- source:
--   Proved ae_injective_of_pairwise_product_law_atomless [c061cb0a-0dbe-4e31-a689-bca418a485bd]. Supports actual canonical Poisson point family in LeanLevy/RandomMeasure/PoissonPointFamily.lean while respecting the zero-mass Dirac fallback.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Theorems.Thm_AvramDividend_Classical_ae_injective_of_pairwise_product_law_atomless

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.ae_injective_on_active_of_pairwise_product_law_atomless
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (active : ι → Prop) (τ : ι → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (hpair : ∀ i j, active i → active j → i ≠ j →
      Measure.map (fun ω => (τ i ω, τ j ω)) P =
        (Measure.map (τ i) P).prod (Measure.map (τ j) P))
    (hatom : ∀ i, active i →
      NullSingletonClass (Measure.map (τ i) P)) :
    ∀ᵐ ω ∂P, Set.InjOn (fun i : ι => τ i ω) {i | active i} := by sorry
