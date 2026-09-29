-- Prove2me | Theorems.Thm_FamousTheorems_besicovitch_covering
-- name    : FamousTheorems.besicovitch_covering
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:45.89187+00:00
-- url     : https://prove2.me/theorems/9e1346af-60f6-4a1d-b689-797f06792ba9
-- title:
--   The Besicovitch covering theorem
-- statement:
--   **The Besicovitch covering theorem (almost-everywhere form).** Let $\alpha$ be a second-countable metric space with the Besicovitch covering property (e.g. $\mathbb R^n$ with any norm), and $\mu$ an s-finite Borel measure. Let $s\subseteq\alpha$, and for each $x\in s$ let $f(x)\subseteq\mathbb R$ be a set of admissible radii containing arbitrarily small positive values, and $R(x)>0$. Then there are a countable $t\subseteq s$ and radii $r(x)\in f(x)\cap(0,R(x))$ such that the closed balls $\overline B(x,r(x))$, $x\in t$, are pairwise disjoint and cover $\mu$-almost all of $s$.
--
--   Unlike Vitali's lemma, no doubling condition on $\mu$ is needed: the geometry of the space alone makes the covering work for every locally finite measure. It is the basis of differentiation of arbitrary Radon measures on $\mathbb R^n$ and of density theorems in geometric measure theory.
--
--   **Formalization note.** Mathlib's `Besicovitch.exists_disjoint_closedBall_covering_ae`; `HasBesicovitchCovering α` asserts the existence of a Besicovitch constant for the space (an instance is provided for finite-dimensional real normed spaces).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Besicovitch.exists_disjoint_closedBall_covering_ae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem besicovitch_covering {α : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [HasBesicovitchCovering α] (μ : MeasureTheory.Measure α) [MeasureTheory.SFinite μ]
    (f : α → Set ℝ) (s : Set α) (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Set.Ioo 0 δ).Nonempty) (R : α → ℝ)
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x ∩ Set.Ioo 0 (R x)) ∧
      μ (s \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 ∧ t.PairwiseDisjoint fun x => Metric.closedBall x (r x) := by sorry

end FamousTheorems
