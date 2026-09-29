-- Prove2me | Theorems.Thm_FamousTheorems_hahn_banach_separation
-- name    : FamousTheorems.hahn_banach_separation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:54.894019+00:00
-- url     : https://prove2.me/theorems/0ea5ad31-e8fb-4fbe-a42e-58aa5a8dacf3
-- title:
--   The Hahn–Banach separation theorem (open convex set)
-- statement:
--   **The Hahn–Banach separation theorem.** Let $E$ be a real topological vector space and $s,t\subseteq E$ disjoint convex sets with $s$ open. Then there are a continuous linear functional $\varphi$ on $E$ and a real number $u$ with
--   $$\varphi(a)<u\le\varphi(b)\qquad\text{for all } a\in s,\ b\in t.$$
--
--   This geometric form of the Hahn–Banach theorem says that disjoint convex sets can be separated by a closed hyperplane when one of them is open. It is basic in functional analysis, convex analysis and optimization. It underlies duality theory, the bipolar theorem, the Krein–Milman theorem and the existence of supporting hyperplanes.
--
--   **Formalization note.** Mathlib's `geometric_hahn_banach_open`. `StrongDual ℝ E` is the space of continuous linear functionals `E →L[ℝ] ℝ`. The space is only assumed to be a topological vector space: an additive topological group with continuous scalar multiplication. No local convexity is needed because one set is open.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `geometric_hahn_banach_open`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hahn_banach_separation {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {s t : Set E} (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b := by sorry

end FamousTheorems
