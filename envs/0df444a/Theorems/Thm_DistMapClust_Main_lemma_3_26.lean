-- Prove2me | Theorems.Thm_DistMapClust_Main_lemma_3_26
-- name    : DistMapClust.Main.lemma_3_26
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:04:06.776735+00:00
-- url     : https://prove2.me/theorems/0bf28d6d-318c-454d-ae8a-58888146e83e
-- title:
--   Lemma 3.26 — a bipartite graph with B-degrees ≥ ab and A-degrees ≤ b has a subgraph with B-degrees ≥ a and A-degrees ≤ 1
-- statement:
--   Let $G=(A\sqcup B,E)$ be a finite bipartite graph and $a,b$ positive integers. If every $v\in B$ has degree at least $ab$ and every $u\in A$ has degree at most $b$, then there is $E'\subseteq E$ such that in $G'=(A\sqcup B,E')$
--   $$\deg_{G'}(v)\ge a\ \ (v\in B),\qquad \deg_{G'}(u)\le1\ \ (u\in A).$$
--   It is a consequence of Hall's theorem and is used to turn a many-to-few charging scheme into a disjoint one in the proof of Lemma 3.28.
--
--   **Formalization Note.** The sides are finite types `A`, `B`; edges are a `Finset (A × B)`; a degree is the number of edges at a vertex.
--
--   Differences from the source:
--   - encoding: bipartite graph G = (A ⊔ B, E), a, b ∈ N_{>0} → finite types A, B, E : Finset (A × B), degrees as numbers of incident edges, 0 < a, 0 < b; reason: Lean convention; the paper's graphs are finite
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), pp. 41–42, Lemma 3.26

import Mathlib

namespace DistMapClust.Main

/-- Lemma 3.26 (pp. 41–42). A finite bipartite graph with sides `A`, `B` and edge set `E ⊆ A × B`
in which every vertex of `B` has degree at least `ab` and every vertex of `A` degree at most `b` has
a set of edges `E' ⊆ E` in which every vertex of `B` has degree at least `a` and every vertex of `A`
degree at most `1`. -/
theorem lemma_3_26 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hB : ∀ v : B, a * b ≤ (E.filter (fun e => e.2 = v)).card)
    (hA : ∀ u : A, (E.filter (fun e => e.1 = u)).card ≤ b) :
    ∃ E' ⊆ E, (∀ v : B, a ≤ (E'.filter (fun e => e.2 = v)).card) ∧
      ∀ u : A, (E'.filter (fun e => e.1 = u)).card ≤ 1 := by sorry

end DistMapClust.Main
