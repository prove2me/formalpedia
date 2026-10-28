-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_injective_active_arrivals_of_product_restricted_pair_laws
-- name    : AvramDividend.Classical.ae_injective_active_arrivals_of_product_restricted_pair_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:15:45.591299+00:00
-- url     : https://prove2.me/theorems/cf386081-17b1-4e5c-a681-dcc67a15fc02
-- title:
--   Collision-free active Poisson arrival times from diffuse product laws conditional on joint activity
-- statement:
--   A countable random active subset of potential Poisson arrivals has pairwise distinct arrival times almost surely when, for each distinct pair i,j, its restricted joint time law is a product μ_ij×ν_ij with s-finite diffuse second marginal ν_ij. The diffuse law is allowed to vary with the pair, reflecting distinct normalised Poisson partition-piece distributions. The theorem combines the product-measure diagonal null identity, restriction almost-everywhere implication and countable simultaneous active noncollision, without claiming these restricted product laws have already been established for the actual LeanLevy family.
-- source:
--   Proved ae_distinct_of_joint_product_atomless [e64d957a-0ab9-4e20-aa96-d98a7a18cd21], ae_injective_on_active_indices_of_pairwise_ae [9e7b4e2f-da94-43db-b29f-bd0df495eec2], pinned Mathlib ae_restrict_iff; LeanLevy PoissonPointFamily.lean coordinate laws depend on partition piece k.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_ae_injective_on_active_indices_of_pairwise_ae
import Theorems.Thm_AvramDividend_Classical_ae_distinct_of_joint_product_atomless

open AvramDividend.Classical MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.ae_injective_active_arrivals_of_product_restricted_pair_laws
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (active : ι → Ω → Prop) (τ : ι → Ω → ℝ)
    (hactive : ∀ i, MeasurableSet {ω : Ω | active i ω})
    (hmeas : ∀ i j, Measurable (fun ω : Ω => (τ i ω, τ j ω)))
    (μ ν : ι → ι → Measure ℝ)
    (hSFinite : ∀ i j, SFinite (ν i j))
    (hNull : ∀ i j, NullSingletonClass (ν i j))
    (hjoint : ∀ i j : ι, i ≠ j →
      (P.restrict {ω : Ω | active i ω ∧ active j ω}).map
        (fun ω => (τ i ω, τ j ω)) = (μ i j).prod (ν i j)) :
    ∀ᵐ ω ∂P, ∀ i j : ι,
      active i ω → active j ω → τ i ω = τ j ω → i = j := by sorry
