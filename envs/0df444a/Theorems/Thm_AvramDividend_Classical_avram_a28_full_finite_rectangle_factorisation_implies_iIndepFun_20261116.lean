-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
-- name    : AvramDividend.Classical.avram_a28_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-16T12:31:28.948479+00:00
-- url     : https://prove2.me/theorems/10eff762-979f-4cbc-bf43-7d7f4bf84817
-- title:
--   Full finite measurable rectangle probability factorisation implies jointly independent random variables
-- statement:
--   A full-dimensional rectangle probability product identity for all measurable sets on a finite family implies the standard Mathlib iIndepFun property. For an arbitrary subset of coordinates, fill all omitted coordinates with the full measurable set, then simplify the events and products. This is the genuine finite-dimensional bridge needed after Proved chronological prefix factorisation, and keeps the original probability measure.
-- source:
--   Pinned Mathlib ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul and Finset.prod_ite_mem.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a28_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (n : ℕ) (Y : ℕ → Ω → E)
    (hFull : ∀ (A : Fin n → Set E),
      (∀ i, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        ∏ i : Fin n, P (Y i.val ⁻¹' A i)) :
    iIndepFun (fun i : Fin n => Y i.val) P := by sorry
