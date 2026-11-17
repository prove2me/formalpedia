-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_probability_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
-- name    : AvramDividend.Classical.avram_a28_probability_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:37:26.13594+00:00
-- url     : https://prove2.me/theorems/b9e6b975-ec04-4f67-af77-5167dfa59e54
-- title:
--   Full finite rectangle factorisation under a probability measure implies mutually independent variables
-- statement:
--   Assume explicitly IsProbabilityMeasure P. A full-dimensional rectangle probability product identity on Fin n then implies the standard mutual independence property, including the omitted-coordinate event factors P(univ)=1. The probability assumption repairs a real gap in the earlier under-specified version.
-- source:
--   Pinned Mathlib ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul and Finset.prod_ite_mem.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a28_probability_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (Y : ℕ → Ω → E)
    (hFull : ∀ (A : Fin n → Set E),
      (∀ i, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        ∏ i : Fin n, P (Y i.val ⁻¹' A i)) :
    iIndepFun (fun i : Fin n => Y i.val) P := by sorry
