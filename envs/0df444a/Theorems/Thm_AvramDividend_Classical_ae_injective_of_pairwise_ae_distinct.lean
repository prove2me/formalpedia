-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_injective_of_pairwise_ae_distinct
-- name    : AvramDividend.Classical.ae_injective_of_pairwise_ae_distinct
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:59:21.494821+00:00
-- url     : https://prove2.me/theorems/9879b1ce-36c2-4090-b718-63286f19194f
-- title:
--   Pairwise almost-surely distinct countably indexed random arrival times are jointly injective almost surely
-- statement:
--   Let a family of random values τ_i(ω) be indexed by a countable set I. If for every fixed pair i≠j their values differ almost surely, then outside one common null set all indices have distinct values simultaneously: i↦τ_i(ω) is injective almost surely. This is a countable-union-of-null-events theorem needed to upgrade pairwise diffuse Poisson time-coordinate laws to collision-free canonical marked arrivals at all times. It does not assert the still-missing pairwise null-collision property for the concrete LeanLevy point family.
-- source:
--   Pinned Mathlib ae_all_iff and countability, as used in Proved ae_isCadlag_bandJumpSum in LeanLevy/RandomMeasure/LevyJumpPath.lean.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.IdentDistrib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.ae_injective_of_pairwise_ae_distinct
    {Ω ι α : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (τ : ι → Ω → α)
    (hpair : ∀ i j : ι, i ≠ j → ∀ᵐ ω ∂P, τ i ω ≠ τ j ω) :
    ∀ᵐ ω ∂P, Function.Injective (fun i : ι => τ i ω) := by sorry
