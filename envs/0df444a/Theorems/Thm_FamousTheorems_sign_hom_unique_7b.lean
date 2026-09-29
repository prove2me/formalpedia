-- Prove2me | Theorems.Thm_FamousTheorems_sign_hom_unique_7b
-- name    : FamousTheorems.sign_hom_unique_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:17.235982+00:00
-- url     : https://prove2.me/theorems/be8deabc-5e0c-4864-ac06-4d04bd6a25a7
-- title:
--   Uniqueness of the sign homomorphism on Sₙ
-- statement:
--   **Uniqueness of the sign homomorphism.** Let $\alpha$ be a finite set and $s:\operatorname{Sym}(\alpha)\to\{\pm1\}$ a surjective group homomorphism. Then $s$ is the sign homomorphism.
--
--   So the sign is the only nontrivial homomorphism from a symmetric group to $\{\pm1\}$; equivalently, $A_n$ is the only subgroup of index $2$ in $S_n$. This characterization is used to identify the sign in other guises, such as the determinant of a permutation matrix or the parity of the number of inversions. The proof uses that all transpositions are conjugate and generate the group, so $s$ takes the same value $-1$ on each of them.
--
--   **Formalization note.** Mathlib's `Equiv.Perm.eq_sign_of_surjective_hom`. `ℤˣ` is the group of units of $\mathbb Z$, which is $\{\pm1\}$, and `Equiv.Perm.sign` is the sign homomorphism.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Equiv.Perm.eq_sign_of_surjective_hom`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sign_hom_unique_7b {α : Type*} [DecidableEq α] [Fintype α] (s : Equiv.Perm α →* ℤˣ) (hs : Function.Surjective s) :
    s = Equiv.Perm.sign := by sorry

end FamousTheorems
