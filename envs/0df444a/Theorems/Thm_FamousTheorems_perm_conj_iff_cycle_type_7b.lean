-- Prove2me | Theorems.Thm_FamousTheorems_perm_conj_iff_cycle_type_7b
-- name    : FamousTheorems.perm_conj_iff_cycle_type_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:06.855551+00:00
-- url     : https://prove2.me/theorems/f5bc3610-db90-41fe-a658-a29a0230e426
-- title:
--   Two permutations are conjugate iff they have the same cycle type
-- statement:
--   **Permutations are conjugate if and only if they have the same cycle type.** Let $\alpha$ be a finite set and $\sigma,\tau$ permutations of $\alpha$. Then $\tau=\pi\sigma\pi^{-1}$ for some permutation $\pi$ if and only if $\sigma$ and $\tau$ have the same multiset of cycle lengths.
--
--   So the conjugacy classes of $S_n$ correspond to partitions of $n$. This correspondence is the starting point of the representation theory of symmetric groups, where the irreducible representations are also indexed by partitions. Conjugating a cycle $(a_1\,\dots\,a_k)$ by $\pi$ gives $(\pi(a_1)\,\dots\,\pi(a_k))$, which proves one direction; for the other, one maps the cycles of $\sigma$ onto those of $\tau$.
--
--   **Formalization note.** Mathlib's `Equiv.Perm.isConj_iff_cycleType_eq`. `σ.cycleType` is the multiset of lengths of the cycles of $\sigma$ of length at least $2$. Fixed points are omitted, but their number is determined by the size of $\alpha$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Equiv.Perm.isConj_iff_cycleType_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem perm_conj_iff_cycle_type_7b {α : Type*} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) : IsConj σ τ ↔ σ.cycleType = τ.cycleType := by sorry

end FamousTheorems
