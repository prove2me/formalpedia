-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_countable_cap_germs_to_finite_raw_clock_ws01c
-- name    : AvramDividend.Classical.bv_countable_cap_germs_to_finite_raw_clock_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:49:56.601832+00:00
-- url     : https://prove2.me/theorems/c3df14c8-429b-411a-9a96-89965bf8f207
-- title:
--   Almost-sure right germs at every integer cap imply a right germ at the finite raw clock
-- statement:
--   Given an arbitrary extended nonnegative random clock τ and a path property G of a finite time, if G holds almost surely at each natural-number cap of τ, then G holds almost surely at the raw clock on the event τ<∞. The proof combines countably many full-measure events, embeds the finite raw ENNReal time via toNNReal, uses an integer cap larger than that finite time, and simplifies the capped clock to the raw clock. No assertion is made at an infinite clock.
-- source:
--   Cause-linked repair of failed terminal authoring job 47dae5ba-263f-4d0c-8f2b-758fe41cd21b: removed invalid `open AvramDividend.Classical` namespace and broadened import to Mathlib for Measure and ae_all_iff. Original formal statement and proof preserved; complete 27-line solution work/avram_ws01c_uncap_countable_germs_solution_pub_repair_20261028.lean.

import Mathlib

open Filter MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_countable_cap_germs_to_finite_raw_clock_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ≥0∞)
    (G : ℝ≥0 → Ω → Prop)
    (hCap : ∀ N : ℕ, ∀ᵐ ω ∂P,
      G ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω) :
    ∀ᵐ ω ∂P,
      τ ω < ⊤ → G (τ ω).toNNReal ω := by sorry
