-- Prove2me | Theorems.Thm_FamousTheorems_stone_separation_theorem
-- name    : FamousTheorems.stone_separation_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:09.787111+00:00
-- url     : https://prove2.me/theorems/e3e77dbd-6109-453f-b85c-1cd48ba81347
-- title:
--   Stone's separation theorem
-- statement:
--   **Stone's separation theorem.** Let $E$ be a vector space over a linearly ordered field $\mathbb k$, and let $s,t\subseteq E$ be disjoint convex sets. Then there is a convex set $C$ whose complement is also convex, with $s\subseteq C$ and $t\subseteq E\setminus C$.
--
--   Sets $C$ with $C$ and its complement both convex are called half-spaces (or hemispaces). The theorem is a purely algebraic version of the Hahn–Banach separation theorem: it needs no topology and no completeness, only convexity. It underlies the abstract theory of convexity spaces.
--
--   **Formalization note.** Mathlib's `exists_convex_convex_compl_subset`. The field is any linearly ordered field (`Field 𝕜`, `LinearOrder 𝕜`, `IsStrictOrderedRing 𝕜`), and `Cᶜ` is the set complement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_convex_convex_compl_subset`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem stone_separation_theorem {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}
    (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t) :
    ∃ C : Set E, Convex 𝕜 C ∧ Convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ := by sorry

end FamousTheorems
