-- Prove2me | Theorems.Thm_FamousTheorems_caratheodory_criterion
-- name    : FamousTheorems.caratheodory_criterion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:27.362866+00:00
-- url     : https://prove2.me/theorems/b7f9c266-84a1-4c0b-aa90-c4b916222b40
-- title:
--   Carathéodory's theorem (measure theory)
-- statement:
--   **Carathéodory's theorem (measure theory).** Let $m$ be an outer measure on a set $X$. A set $s$ is called $m$-measurable if it splits every set additively: $m(t)=m(t\cap s)+m(t\setminus s)$ for all $t$. The $m$-measurable sets form a σ-algebra, and $m$ is countably additive on it:
--   $$m\Big(\bigcup_i s_i\Big)=\sum_i m(s_i)\quad\text{for pairwise disjoint measurable }s_i .$$
--
--   This is the construction behind almost every measure in analysis: Lebesgue measure, Lebesgue–Stieltjes measures, Hausdorff measures, and the Carathéodory extension of a premeasure from an algebra of sets.
--
--   **Formalization note.** Mathlib's `MeasureTheory.OuterMeasure.caratheodory` is the σ-algebra of $m$-measurable sets (a `MeasurableSpace`, so being a σ-algebra is built into its type). The statement combines `MeasureTheory.OuterMeasure.isCaratheodory_iff` (its sets are exactly the splitting sets) and `MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory` (countable additivity).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.OuterMeasure.iUnion_eq_of_caratheodory`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped MeasureTheory

theorem caratheodory_criterion {α : Type*} (m : MeasureTheory.OuterMeasure α) :
    (∀ s : Set α, MeasurableSet[m.caratheodory] s ↔ ∀ t, m t = m (t ∩ s) + m (t \ s)) ∧
      ∀ s : ℕ → Set α, (∀ i, MeasurableSet[m.caratheodory] (s i)) → Pairwise (Function.onFun Disjoint s) →
        m (⋃ i, s i) = ∑' i, m (s i) := by sorry

end FamousTheorems
