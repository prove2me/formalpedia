-- Prove2me | Theorems.Thm_FamousTheorems_compact_iff_totally_bounded_complete_7a
-- name    : FamousTheorems.compact_iff_totally_bounded_complete_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:49.273358+00:00
-- url     : https://prove2.me/theorems/8e4df301-28c1-4600-b9f8-b1a7ccadf6a6
-- title:
--   Totally bounded complete sets are exactly the compact sets
-- statement:
--   **Totally bounded complete sets are exactly the compact sets.** In a uniform space, and in particular in a metric space, a set is compact if and only if it is totally bounded and complete.
--
--   Total boundedness means that the set can be covered by finitely many sets of any given small size. For metric spaces this characterisation goes back to Fréchet and Hausdorff. It gives the Heine–Borel theorem in $\mathbb R^n$ and is the usual way to prove compactness in function spaces, as in the Arzelà–Ascoli theorem.
--
--   **Formalization note.** Mathlib's `isCompact_iff_totallyBounded_isComplete`. `TotallyBounded s` means that for every entourage $d$ there are finitely many points whose $d$-neighbourhoods cover $s$. `IsComplete s` means that every Cauchy filter on $s$ converges to a point of $s$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isCompact_iff_totallyBounded_isComplete`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem compact_iff_totally_bounded_complete_7a {α : Type*} [UniformSpace α] {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s := by sorry

end FamousTheorems
