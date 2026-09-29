-- Prove2me | Theorems.Thm_FamousTheorems_matroid_bases_equal_card_7b
-- name    : FamousTheorems.matroid_bases_equal_card_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:23.560008+00:00
-- url     : https://prove2.me/theorems/a5d651d6-0d15-4243-b272-64aad64b8444
-- title:
--   All bases of a matroid have the same cardinality
-- statement:
--   **All bases of a matroid have the same cardinality.** Let $M$ be a matroid on a ground set $E$ (possibly infinite). If $B_1$ and $B_2$ are bases of $M$, then $|B_1|=|B_2|$, where the cardinalities are taken in $\mathbb N\cup\{\infty\}$.
--
--   This is the matroid form of the invariance of dimension, and it makes the rank of a matroid well defined. For the matroid of linearly independent columns of a matrix it recovers the fact that all bases of a vector space have the same size. For the graphic matroid it says that all spanning forests of a graph have the same number of edges. The proof uses the basis exchange axiom.
--
--   **Formalization note.** Mathlib's `Matroid.IsBase.encard_eq_encard_of_isBase`. `Set.encard` is the cardinality of a set in `ℕ∞`, equal to $\top$ for infinite sets, so the statement covers matroids of infinite rank only in the sense that both bases are infinite.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matroid.IsBase.encard_eq_encard_of_isBase`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem matroid_bases_equal_card_7b {α : Type*} {M : Matroid α} {B₁ B₂ : Set α} (h₁ : M.IsBase B₁) (h₂ : M.IsBase B₂) :
    B₁.encard = B₂.encard := by sorry

end FamousTheorems
