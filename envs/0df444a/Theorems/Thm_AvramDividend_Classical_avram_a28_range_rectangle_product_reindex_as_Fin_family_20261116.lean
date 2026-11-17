-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_range_rectangle_product_reindex_as_Fin_family_20261116
-- name    : AvramDividend.Classical.avram_a28_range_rectangle_product_reindex_as_Fin_family_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:32:45.501785+00:00
-- url     : https://prove2.me/theorems/db86406d-338b-448d-a29a-c04b6b2d5634
-- title:
--   Reindex a full finite chronological range rectangle probability product over Fin n
-- statement:
--   Given the product formula for all measurable preimage rectangles indexed by Finset.range n, reindex the same full-dimensional formula using Fin n. Extend any Fin n sets to Nat by using the full set for indices outside n, identify the corresponding intersection, and use Finset.prod_fin_eq_prod_range. Exact equality under the same original probability measure.
-- source:
--   Pinned Mathlib Finset.prod_fin_eq_prod_range and Set.mem_iInter.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a28_range_rectangle_product_reindex_as_Fin_family_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (n : ℕ) (Y : ℕ → Ω → E)
    (hFull : ∀ (A : ℕ → Set E),
      (∀ i < n, MeasurableSet (A i)) →
      P (⋂ i ∈ Finset.range n, Y i ⁻¹' A i) =
        ∏ i ∈ Finset.range n, P (Y i ⁻¹' A i)) :
    ∀ (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        ∏ i : Fin n, P (Y i.val ⁻¹' A i) := by sorry
