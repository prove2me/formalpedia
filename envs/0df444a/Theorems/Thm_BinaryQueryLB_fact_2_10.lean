-- Prove2me | Theorems.Thm_BinaryQueryLB_fact_2_10
-- name    : BinaryQueryLB.fact_2_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:43:11.020771+00:00
-- url     : https://prove2.me/theorems/4d8e03f4-4537-4129-b1db-38802d76e7dc
-- title:
--   Fact 2.10 — $E\mapsto\mu^*(P\cap E)$ is a finite measure on Lebesgue-measurable sets
-- statement:
--   Let $P\subseteq\mathbb R^m$ be bounded (not necessarily measurable), and let $\mu^*$ be Lebesgue outer measure. Then $\nu_P(E)=\mu^*(P\cap E)$ is a finite measure on the Lebesgue-measurable subsets $E$ of $\mathbb R^m$, with
--   $$
--   \nu_P(\mathbb R^m)=\mu^*(P),\qquad \nu_P(E)\le\mathrm{vol}_m(E).
--   $$
--   Explicitly: $\nu_P(\emptyset)=0$; for pairwise disjoint Lebesgue-measurable $E_1,E_2,\dots$, $\mu^*(P\cap\bigcup_kE_k)=\sum_k\mu^*(P\cap E_k)$; $\mu^*(P)<\infty$; and $\mu^*(P\cap E)\le\mathrm{vol}_m(E)$ for every Lebesgue-measurable $E$.
--
--   This is what allows the adversary to work with non-measurable sets of rows.
--
--   Differences from the source:
--   - generalization: P ⊆ ℝ^m with m ≥ 1 → any dimension m : ℕ; reason: the case m = 0 is included; every m ≥ 1 is covered
--   - encoding: Lebesgue outer measure µ* → MeasureTheory.volume evaluated on arbitrary sets, values in ℝ≥0∞; reason: volume on an arbitrary set is its outer measure
--   - encoding: ν_P is a finite measure on the Lebesgue-measurable sets → ν_P(∅) = 0, countable additivity over pairwise disjoint null-measurable sequences, and µ*(P) < ∞; reason: the definition of a finite measure; Lebesgue-measurable is NullMeasurableSet for volume
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Fact 2.10, p.15

import Mathlib

namespace BinaryQueryLB

/-- **Fact 2.10 (outer measure restricted to a set).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Fact 2.10, p.15: "Let `P ⊆ R^m` be
bounded. Then `ν_P(E) = µ*(P ∩ E)` is a finite measure on the Lebesgue-measurable subsets `E` of
`R^m`, with `ν_P(R^m) = µ*(P)` and `ν_P(E) ≤ vol_m(E)`."

**Formalization Note.** `µ*` is `volume` on `EuclideanSpace ℝ (Fin m)` evaluated on arbitrary sets
(Lebesgue outer measure); `P` is not assumed measurable. "Lebesgue-measurable" is
`NullMeasurableSet` for `volume`. "A finite measure" is stated as: `ν_P(∅) = 0`, countable
additivity over pairwise disjoint sequences of Lebesgue-measurable sets, and `ν_P(R^m) < ∞`. The
dimension `m` is arbitrary. -/
theorem fact_2_10 (m : ℕ) (P : Set (EuclideanSpace ℝ (Fin m))) (hP : Bornology.IsBounded P) :
    MeasureTheory.volume (P ∩ ∅) = 0 ∧
      (∀ E : ℕ → Set (EuclideanSpace ℝ (Fin m)),
        (∀ k, MeasureTheory.NullMeasurableSet (E k) MeasureTheory.volume) →
        Pairwise (Function.onFun Disjoint E) →
          MeasureTheory.volume (P ∩ ⋃ k, E k) = ∑' k, MeasureTheory.volume (P ∩ E k)) ∧
      MeasureTheory.volume (P ∩ Set.univ) = MeasureTheory.volume P ∧
      MeasureTheory.volume P < ⊤ ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin m)), MeasureTheory.NullMeasurableSet E MeasureTheory.volume →
        MeasureTheory.volume (P ∩ E) ≤ MeasureTheory.volume E := by sorry

end BinaryQueryLB
