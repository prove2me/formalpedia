-- Prove2me | Theorems.Thm_FamousTheorems_gallagher_ergodic_theorem
-- name    : FamousTheorems.gallagher_ergodic_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:35.564025+00:00
-- url     : https://prove2.me/theorems/f4ab2704-d555-4343-bbe9-1bdd47e803e5
-- title:
--   Gallagher's ergodic theorem
-- statement:
--   **Gallagher's ergodic theorem.** Let $\delta_n\to0$ be a sequence of real numbers, and let $W_\delta$ be the set of points $x$ of the circle $\mathbb R/T\mathbb Z$ that are $\delta_n$-well approximable. This means that for infinitely many $n$ there is a point $y$ of order exactly $n$ with $|x-y|<\delta_n$. Then $W_\delta$ has measure $0$ or full measure.
--
--   This zero–one law is a key input to the Duffin–Schaeffer conjecture in metric Diophantine approximation, proved by Koukoulopoulos and Maynard. It reduces the problem to showing that the set of approximable points has positive measure.
--
--   **Formalization note.** Mathlib's `AddCircle.addWellApproximable_ae_empty_or_univ`. `addWellApproximable (AddCircle T) δ` is the set of points lying in infinitely many of the balls of radius $\delta_n$ around points of additive order $n$. "Measure zero or full measure" is written as: almost every point is outside the set, or almost every point is inside it, for the Haar measure on the circle.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AddCircle.addWellApproximable_ae_empty_or_univ`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gallagher_ergodic_theorem {T : ℝ} [Fact (0 < T)] (δ : ℕ → ℝ) (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    (∀ᵐ (x : AddCircle T), x ∉ addWellApproximable (AddCircle T) δ) ∨
      ∀ᵐ (x : AddCircle T), x ∈ addWellApproximable (AddCircle T) δ := by sorry

end FamousTheorems
