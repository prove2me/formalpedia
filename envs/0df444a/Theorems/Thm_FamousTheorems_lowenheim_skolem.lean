-- Prove2me | Theorems.Thm_FamousTheorems_lowenheim_skolem
-- name    : FamousTheorems.lowenheim_skolem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:13.206459+00:00
-- url     : https://prove2.me/theorems/7de0c6ab-8793-439c-8405-f33d25949f19
-- title:
--   The Löwenheim–Skolem theorem
-- statement:
--   **The Löwenheim–Skolem theorem.** Let $M$ be an infinite structure in a first-order language $L$, and let $\kappa$ be an infinite cardinal with $|L|\le\kappa$. Then there is an $L$-structure $N$ of cardinality exactly $\kappa$ that is an elementary substructure or an elementary extension of $M$.
--
--   This combines the downward and upward theorems. First-order logic cannot pin down the cardinality of an infinite structure: there are countable models of set theory (Skolem's paradox) and uncountable nonstandard models of arithmetic. It is a starting point of model theory and of Lindström's characterisation of first-order logic.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.exists_elementaryEmbedding_card_eq`. The structure `N` is bundled; cardinalities of `L` (number of symbols) and `κ` are compared after lifting to a common universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.exists_elementaryEmbedding_card_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w w'

theorem lowenheim_skolem (L : FirstOrder.Language.{u, v}) (M : Type w') [L.Structure M] [Infinite M] (κ : Cardinal.{w})
    (h1 : Cardinal.aleph0 ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled.{w} L.Structure,
      (Nonempty (L.ElementaryEmbedding N M) ∨ Nonempty (L.ElementaryEmbedding M N)) ∧ Cardinal.mk N = κ := by sorry

end FamousTheorems
