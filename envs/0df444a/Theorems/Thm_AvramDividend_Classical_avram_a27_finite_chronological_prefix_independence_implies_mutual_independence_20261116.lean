-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
-- name    : AvramDividend.Classical.avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:38:34.334223+00:00
-- url     : https://prove2.me/theorems/0770ead1-c61d-4ed0-acd5-71acd48dac45
-- title:
--   Chronological independence from every finite prefix implies mutual independence of the finite family
-- statement:
--   For a finite chronological family of measurable random variables on one probability space, if each new variable Y_k is independent of the entire tuple (Y_0,...,Y_{k-1}) under the same original P, then the family Y_0,...,Y_{n-1} is mutually independent (iIndepFun). Prove by induction / finite-dimensional product measures or the pinned Mathlib iIndepFun_iff_measure_inter_preimage_eq_mul. This is a generic honest finite-prefix-to-mutual-independence bridge for original physical Lévy marked-cell counts, not a Poisson companion.
-- source:
--   Classical independence equivalence and induction; pinned Mathlib ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → E)
    (hMeas : ∀ i < n, Measurable (Y i))
    (hPrefix : ∀ k < n,
      IndepFun (fun ω : Ω => fun i : Fin k => Y i.val ω)
        (Y k) P) :
    iIndepFun (fun i : Fin n => Y i.val) P := by sorry
