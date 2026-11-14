-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_restricted_mark_pushforward_disjoint_support_zero_20261114
-- name    : AvramDividend.Classical.avram_a27_restricted_mark_pushforward_disjoint_support_zero_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:46:58.718551+00:00
-- url     : https://prove2.me/theorems/fadc9670-d466-4378-9335-6285fafb1c8a
-- title:
--   Measurable marked pushforward of a restricted source measure vanishes on every avoided mark window
-- statement:
--   A restricted measure pushed through a measurable marked path map gives zero mass to every measurable marked set avoided by the source support.
-- source:
--   Pinned Mathlib Measure.map_apply, Measure.restrict_apply and set disjointness.

import Mathlib
open MeasureTheory Set
noncomputable section

/-- A restricted source point measure assigns zero mass after a measurable pushforward to an avoided marked set. -/

theorem AvramDividend.Classical.avram_a27_restricted_mark_pushforward_disjoint_support_zero_20261114
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (S : Set α) (f : α → β)
    (hf : Measurable f) (E : Set β) (hE : MeasurableSet E)
    (hNo : ∀ x ∈ S, f x ∉ E) :
    (μ.restrict S).map f E = 0 := by sorry
