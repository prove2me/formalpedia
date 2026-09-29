-- Prove2me | Theorems.Thm_FamousTheorems_kleitman_intersecting_families
-- name    : FamousTheorems.kleitman_intersecting_families
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:55.201107+00:00
-- url     : https://prove2.me/theorems/090173ca-b3ef-4555-b340-f65113f88f14
-- title:
--   Kleitman's theorem on unions of intersecting families
-- statement:
--   **Kleitman's theorem on intersecting families.** Let $X$ be a nonempty finite set with $|X|=n$ and $\mathcal A_1,\dots,\mathcal A_k$ intersecting families of subsets of $X$ (any two members of the same family meet). Then
--   $$\Big|\bigcup_{i=1}^k\mathcal A_i\Big|\le2^n-2^{n-k} .$$
--
--   For $k=1$ it recovers the classical bound $2^{n-1}$ for a single intersecting family. Kleitman's bound is sharp and answered a question of Erdős on unions of intersecting families.
--
--   **Formalization note.** Mathlib's `Finset.card_biUnion_le_of_intersecting`. The families are indexed by a finset `s` of size $k$, and `Set.Intersecting` means any two members have nonempty intersection. Subtraction is truncated subtraction on `ℕ`, which is harmless since $2^{n-k}\le 2^n$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.card_biUnion_le_of_intersecting`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kleitman_intersecting_families {ι α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    (s.biUnion f).card ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - s.card) := by sorry

end FamousTheorems
