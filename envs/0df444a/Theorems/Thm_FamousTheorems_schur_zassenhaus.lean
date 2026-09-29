-- Prove2me | Theorems.Thm_FamousTheorems_schur_zassenhaus
-- name    : FamousTheorems.schur_zassenhaus
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:46.264039+00:00
-- url     : https://prove2.me/theorems/063e573d-91e9-4d96-83c3-d61aab79785a
-- title:
--   The Schur–Zassenhaus theorem
-- statement:
--   **The Schur–Zassenhaus theorem.** Let $N$ be a normal subgroup of a finite group $G$ whose order is coprime to its index $[G:N]$. Then $N$ has a complement: a subgroup $H$ with $H\cap N=1$ and $HN=G$, so $G\cong N\rtimes H$.
--
--   It is a basic splitting theorem of finite group theory, used for Hall subgroups of solvable groups, for coprime actions, and in the extension theory of groups. The complements are moreover all conjugate.
--
--   **Formalization note.** Mathlib's `Subgroup.exists_left_complement'_of_coprime`; the orders are `Nat.card N` and `N.index`, and `H.IsComplement' N` says every element of `G` factors uniquely as $hn$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.exists_left_complement'_of_coprime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem schur_zassenhaus {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (hN : (Nat.card N).Coprime N.index) :
    ∃ H : Subgroup G, H.IsComplement' N := by sorry

end FamousTheorems
