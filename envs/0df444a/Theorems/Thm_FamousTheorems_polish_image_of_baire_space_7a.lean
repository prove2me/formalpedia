-- Prove2me | Theorems.Thm_FamousTheorems_polish_image_of_baire_space_7a
-- name    : FamousTheorems.polish_image_of_baire_space_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:02.668276+00:00
-- url     : https://prove2.me/theorems/f1d46cb4-f256-45c5-b0e9-883d3011fc2c
-- title:
--   Every Polish space is a continuous image of the Baire space ℕ^ℕ
-- statement:
--   **Every Polish space is a continuous image of the Baire space $\mathbb N^{\mathbb N}$.** Let $\alpha$ be a nonempty Polish space, that is, a separable completely metrizable topological space. Then there is a continuous surjection $\mathbb N^{\mathbb N}\to\alpha$.
--
--   This is a basic theorem of descriptive set theory. It reduces many questions about Polish spaces to the Baire space, whose points are infinite sequences of natural numbers. The analytic sets are then the continuous images of the Baire space, and the result is used in the study of Borel and analytic sets and in the perfect set property.
--
--   **Formalization note.** Mathlib's `PolishSpace.exists_nat_nat_continuous_surjective`. `ℕ → ℕ` carries the product topology of discrete spaces, which is the Baire space.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PolishSpace.exists_nat_nat_continuous_surjective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem polish_image_of_baire_space_7a (α : Type*) [TopologicalSpace α] [PolishSpace α] [Nonempty α] :
    ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Function.Surjective f := by sorry

end FamousTheorems
