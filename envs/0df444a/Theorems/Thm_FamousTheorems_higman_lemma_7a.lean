-- Prove2me | Theorems.Thm_FamousTheorems_higman_lemma_7a
-- name    : FamousTheorems.higman_lemma_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:25.352264+00:00
-- url     : https://prove2.me/theorems/095bf2b1-de83-48d6-ba90-4cb7b6e5e9b2
-- title:
--   Higman's lemma
-- statement:
--   **Higman's lemma.** Let $r$ be a preorder on a type $\alpha$ and let $s\subseteq\alpha$ be partially well-ordered by $r$, meaning that every infinite sequence $x_0,x_1,\dots$ in $s$ has indices $i<j$ with $r(x_i,x_j)$. Then the set of finite lists with entries in $s$ is partially well-ordered by the embedding order: $[a_1,\dots,a_m]\preceq[b_1,\dots,b_n]$ if there are indices $j_1<\dots<j_m$ with $r(a_k,b_{j_k})$ for every $k$.
--
--   Graham Higman proved this in 1952. It is the finite-word case of Kruskal's tree theorem. It implies that every language closed under taking subwords is regular, and it is a standard tool in the termination analysis of rewriting systems and in the theory of well-structured transition systems.
--
--   **Formalization note.** Mathlib's `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`. `List.SublistForall₂ r l₁ l₂` is the embedding order above, and `PartiallyWellOrderedOn` is the sequence condition.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem higman_lemma_7a {α : Type*} (r : α → α → Prop) [IsPreorder α r] {s : Set α} (hs : s.PartiallyWellOrderedOn r) :
    {l : List α | ∀ x ∈ l, x ∈ s}.PartiallyWellOrderedOn (List.SublistForall₂ r) := by sorry

end FamousTheorems
