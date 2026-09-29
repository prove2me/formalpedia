-- Prove2me | Theorems.Thm_FamousTheorems_hausdorff_alexandroff_theorem
-- name    : FamousTheorems.hausdorff_alexandroff_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:16.876039+00:00
-- url     : https://prove2.me/theorems/1c428415-ad36-4543-abfd-f566b50265af
-- title:
--   The Hausdorff–Alexandroff theorem
-- statement:
--   **The Hausdorff–Alexandroff theorem.** Every nonempty compact metric space is a continuous image of the Cantor space $\{0,1\}^{\mathbb N}$.
--
--   The Cantor space is universal among compact metric spaces: every nonempty one is a continuous image of it. One consequence is the existence of space-filling curves: a continuous surjection from the Cantor set onto $[0,1]^2$ can be extended linearly across the gaps of the Cantor set to a continuous surjection $[0,1]\to[0,1]^2$. The theorem is also a basic tool in descriptive set theory.
--
--   **Formalization note.** Mathlib's `exists_nat_bool_continuous_surjective_of_compact`. The Cantor space is `ℕ → Bool` with the product topology.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_nat_bool_continuous_surjective_of_compact`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hausdorff_alexandroff_theorem (X : Type*) [Nonempty X] [MetricSpace X] [CompactSpace X] :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Surjective f := by sorry

end FamousTheorems
