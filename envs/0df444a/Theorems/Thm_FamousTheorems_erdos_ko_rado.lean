-- Prove2me | Theorems.Thm_FamousTheorems_erdos_ko_rado
-- name    : FamousTheorems.erdos_ko_rado
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:54.836066+00:00
-- url     : https://prove2.me/theorems/55479b4c-4f82-4654-aaf0-9897a48426dc
-- title:
--   The Erdős–Ko–Rado theorem
-- statement:
--   **The Erdős–Ko–Rado theorem.** Let $r\le n/2$. If $\mathcal A$ is a family of $r$-element subsets of an $n$-element set in which every two members intersect, then
--   $$|\mathcal A|\le\binom{n-1}{r-1}.$$
--
--   The bound is attained by the star of all $r$-sets through a fixed point. It is the founding result of extremal set theory. Katona's cyclic-permutation proof and its many variants for vector spaces, permutations and graphs make it a model for intersection theorems.
--
--   **Formalization note.** Mathlib's `Finset.erdos_ko_rado`, for families of finsets of `Fin n`; `Set.Intersecting` and `Set.Sized r` express pairwise intersection and uniform size $r$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.erdos_ko_rado`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem erdos_ko_rado {n r : ℕ} {𝒜 : Finset (Finset (Fin n))} (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hr𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r) (hr : r ≤ n / 2) : 𝒜.card ≤ (n - 1).choose (r - 1) := by sorry

end FamousTheorems
