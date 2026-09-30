-- Prove2me | Theorems.Thm_CorrColoring_ThreeChoosable_exists_straight_renaming
-- name    : CorrColoring.ThreeChoosable.exists_straight_renaming
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:04:30.38933+00:00
-- url     : https://prove2.me/theorems/d58a7e0d-5b37-4182-8551-a080e1f1fe8f
-- title:
--   Lemma 7 — straightening a correspondence assignment on a subgraph by renaming
-- statement:
--   Let $G$ be a finite simple graph with a $k$-correspondence assignment $C$, and let $H$ be a subgraph of $G$ such that for every cycle $K$ of $G$ all of whose edges belong to $H$, the assignment $C$ is consistent on $K$ and all edges of $K$ are full in $C$. Then there is a $k$-correspondence assignment $C'$ for $G$ such that
--
--   $$C' \text{ is obtained from } C \text{ by renaming on the vertices of } H, \quad\text{and every edge of } H \text{ is straight in } C'.$$
--
--   In particular this applies whenever $H$ is a forest. The lemma lets later arguments assume that the correspondences along a tree or a triangle are the identity.
--
--   **Formalization Note** "Equivalent to $C$ and obtained from $C$ by renaming on vertices of $H$" is encoded as a family of permutations of $[k]$, trivial outside $V(H)$ (see the definition `IsRenamingOn`). The hypothesis is required for every cycle walk (every starting vertex and direction); for a cycle whose edges are full, consistency from one starting point and direction is equivalent to consistency from all of them, so this is the paper's hypothesis.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 10, Lemma 7

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
import Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn
import Definitions.Def_CorrColoring_ThreeChoosable_Straight

namespace CorrColoring.ThreeChoosable

/-- Lemma 7 (Dvořák–Postle, p. 10). -/
theorem exists_straight_renaming {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} (C : KCorrAssignment G k) (H : G.Subgraph)
    (hH : ∀ (v : V) (K : G.Walk v v), K.IsCycle → (∀ e ∈ K.edges, e ∈ H.edgeSet) →
      ConsistentOn C K ∧ ∀ d ∈ K.darts, Full C d.fst d.snd) :
    ∃ C' : KCorrAssignment G k, IsRenamingOn C C' H.verts ∧
      ∀ u v, H.Adj u v → Straight C' u v := by sorry

end CorrColoring.ThreeChoosable
