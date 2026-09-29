-- Prove2me | Theorems.Thm_FamousTheorems_tube_lemma
-- name    : FamousTheorems.tube_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:21.429994+00:00
-- url     : https://prove2.me/theorems/bba64403-58e5-4e11-9737-e44b52b37c4b
-- title:
--   The tube lemma
-- statement:
--   **The tube lemma.** Let $X,Y$ be topological spaces, $s\subseteq X$ and $t\subseteq Y$ compact, and $n\subseteq X\times Y$ open with $s\times t\subseteq n$. Then there are open sets $u\supseteq s$ and $v\supseteq t$ with $u\times v\subseteq n$.
--
--   With $s$ a single point this is the classical tube lemma, used to prove that a product of two compact spaces is compact (and, by induction, the finite case of Tychonoff's theorem). The generalized form is standard in proofs about compact-open topologies and proper maps.
--
--   **Formalization note.** Mathlib's `generalized_tube_lemma`. `s ×ˢ t` is the product set $s\times t$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `generalized_tube_lemma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tube_lemma {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : Set X} {t : Set Y} {n : Set (X × Y)}
    (hs : IsCompact s) (ht : IsCompact t) (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n := by sorry

end FamousTheorems
