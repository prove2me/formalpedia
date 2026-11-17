-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_chronological_independent_prefix_rectangle_product_20261116
-- name    : AvramDividend.Classical.avram_a27_finite_chronological_independent_prefix_rectangle_product_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:47:40.756474+00:00
-- url     : https://prove2.me/theorems/dfd0a581-7466-4be8-bd6f-93b60d9dbc45
-- title:
--   Chronological finite-prefix independence gives finite Borel-rectangle joint probability factorisation
-- statement:
--   For measurable original-space random variables Y_0,...,Y_(n-1) with each Y_k independent of the entire tuple of earlier variables under the same probability measure, the probability of any intersection of the individual measurable preimage events equals the product of their marginal probabilities. Prove by induction on finite n: split last cell event, identify intersection of previous events as a measurable cylinder set of Fin k→E, apply IndepFun.measure_inter_preimage_eq_mul, then multiply previous factors. This is the exact finite-dimensional core of original physical count mutual independence.
-- source:
--   Pinned Mathlib ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul and measurableSet_pi, finite range induction.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_finite_chronological_independent_prefix_rectangle_product_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → E)
    (hMeas : ∀ i < n, Measurable (Y i))
    (hPrefix : ∀ k < n,
      IndepFun (fun ω : Ω => fun i : Fin k => Y i.val ω)
        (Y k) P)
    (A : ℕ → Set E)
    (hA : ∀ i < n, MeasurableSet (A i)) :
    P (⋂ i ∈ Finset.range n, Y i ⁻¹' A i) =
      ∏ i ∈ Finset.range n, P (Y i ⁻¹' A i) := by sorry
