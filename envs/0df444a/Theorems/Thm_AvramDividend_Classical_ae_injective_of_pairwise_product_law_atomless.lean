-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_injective_of_pairwise_product_law_atomless
-- name    : AvramDividend.Classical.ae_injective_of_pairwise_product_law_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:13:43.817624+00:00
-- url     : https://prove2.me/theorems/c061cb0a-0dbe-4e31-a689-bca418a485bd
-- title:
--   Independent diffuse pairwise random mark arrival times indexed countably are jointly collision free almost surely
-- statement:
--   Given a probability space and a countable family of measurable real arrival times τ_i, suppose distinct indices have product joint distributions and each individual arrival-time law is atomless. Then all arrival times are mutually distinct simultaneously outside one null set. For each distinct i,j, the product law of τ_i,τ_j gives zero probability of the diagonal by diffuse second marginal; pull this result back along the measurable pair map. Apply the accepted countable almost-sure pairwise-distinct-to-injective theorem. This closes a genuine analytical no-time-collision step needed for collision-free canonical Poisson mark-time paths, assuming correct independence and diffuse-time marginal hypotheses.
-- source:
--   Proved prod_ae_distinct_of_atomless_second [830c005e-70db-4c59-9a69-1c1bd94c86d6] and ae_injective_of_pairwise_ae_distinct [9879b1ce-36c2-4090-b718-63286f19194f]. Mathlib MeasureTheory.ae_map_iff. Needed to connect LeanLevy atomless time-coordinate Poisson point families to finite marked step jump-count equals mark-count theorem [0949e0ee-6f6a-4b53-98aa-dec407287daa].

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_prod_ae_distinct_of_atomless_second
import Theorems.Thm_AvramDividend_Classical_ae_injective_of_pairwise_ae_distinct

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.ae_injective_of_pairwise_product_law_atomless
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ι → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (hpair : ∀ i j : ι, i ≠ j →
      Measure.map (fun ω => (τ i ω, τ j ω)) P =
        (Measure.map (τ i) P).prod (Measure.map (τ j) P))
    (hatom : ∀ j : ι, NullSingletonClass (Measure.map (τ j) P)) :
    ∀ᵐ ω ∂P, Function.Injective (fun i : ι => τ i ω) := by sorry
