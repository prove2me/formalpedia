-- Prove2me | Theorems.Thm_ClawFreeChoosable_lemma_12_3_atoms_after_deleting_clique
-- name    : ClawFreeChoosable.lemma_12_3_atoms_after_deleting_clique
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:54.218194+00:00
-- url     : https://prove2.me/theorems/d8a2c4c1-88f0-4a64-bbc9-993a115aa6ea
-- title:
--   Lemma 12.3 — atoms after deleting the prescribed clique
-- statement:
--   Let $G$ be a finite connected graph with no rich clique cutset, and let $S$ be a clique of simplicial vertices of $G$ containing every simplicial vertex of $G$. Then $G - S$ is either empty (that is, $S = V(G)$) or an atom.
--
--   In a minimum counterexample to Theorem 1.3 this makes $G - S$ an atom, to which the Chvátal–Sbihi theorem applies.
--
--   Differences from the source:
--   - encoding: G − S is empty → S = V (Set.univ); G − S is G.induce Sᶜ; reason: Lean convention; same instances
--   - encoding: connected graph → Mathlib's Connected, which includes nonemptiness; reason: for the empty graph G − S is empty and the conclusion holds, so no instance changes
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Lemma 12.3, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsSimplicialClique
import Definitions.Def_ClawFreeChoosable_IsRichCliqueCutset
import Definitions.Def_ClawFreeChoosable_IsAtom

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Lemma 12.3** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.33). Let `G` be a connected graph with no rich clique cutset, and let
`S` be a clique of simplicial vertices containing every simplicial vertex of `G`. Then `G − S` is
either empty or an atom.

**Formalization Note.** `G − S` is `G.induce Sᶜ`; it is empty exactly when `S = V(G)`. Mathlib's
`Connected` is false on the empty graph, for which the conclusion holds trivially. -/
theorem lemma_12_3_atoms_after_deleting_clique {V : Type} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hrich : ¬ ∃ K : Set V, IsRichCliqueCutset G K) (S : Set V)
    (hS : IsSimplicialClique G S) (hall : ∀ v : V, IsSimplicial G v → v ∈ S) :
    S = Set.univ ∨ IsAtom (G.induce Sᶜ) := by sorry

end ClawFreeChoosable
