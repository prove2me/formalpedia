-- Prove2me | Theorems.Thm_FiniteConnectedIntersectionGrouping
-- name    : FiniteConnectedIntersectionGrouping
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:04.899622+00:00
-- url     : https://prove2.me/theorems/f40cd046-8b7e-4252-9f17-1caabf6ad72e
-- title:
--   Finite Connected Intersection Grouping
-- statement:
--   Let $X$ be a topological space, let $s$ be a finite set of indices, and
--   let $\{P_i\}_{i\in s}$ be a finite indexed family of subsets of $X$.
--   Let $K\subseteq X$.  Assume that every $P_i$, $i\in s$, is nonempty,
--   connected, and contained in $K$.  Put an adjacency relation on $s$ by
--   joining $i$ to $j$ when $P_i\cap P_j\ne\varnothing$, and group indices
--   by the reflexive-transitive closure of this nonempty-intersection relation.
--
--   Then there is a finite family of grouped unions, together with for each
--   $i\in s$ a grouped union $G_i$, such that
--   $$
--     G_i=\bigcup_{\substack{j\in s\\ i\leadsto j}} P_j,
--   $$
--   where $i\leadsto j$ means that $j$ is reachable from $i$ by a finite
--   chain of nonempty intersections.  Every grouped union in the finite family is
--   one of the $G_i$'s, every $G_i$ belongs to the finite family, and every
--   member of the finite family is nonempty, connected, and contained in $K$.
--   Moreover $P_i\subseteq G_i$ for every $i\in s$, so any point lying in a
--   raw piece lies in the grouped union attached to that raw piece.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteConnectedIntersectionGrouping`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteConnectedIntersectionGrouping.lean#L1-L102

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

lemma FiniteConnectedIntersectionGrouping
    {X : Type*} [TopologicalSpace X]
    {ι : Type*}
    (s : Finset ι) (piece : ι → Set X) (K : Set X)
    (hpiece_nonempty : ∀ i, i ∈ s → (piece i).Nonempty)
    (hpiece_connected : ∀ i, i ∈ s → IsConnected (piece i))
    (hpiece_subset : ∀ i, i ∈ s → piece i ⊆ K) :
    ∃ groupedPieces : Finset (Set X),
      ∃ groupOf : ι → Set X,
        (∀ i, i ∈ s →
          groupOf i =
            ⋃ j ∈
              ({j : ι | j ∈ s ∧
                Relation.ReflTransGen
                  (fun u v : ι => u ∈ s ∧ v ∈ s ∧
                    (piece u ∩ piece v).Nonempty) i j} : Set ι),
              piece j) ∧
        (∀ i, i ∈ s → groupOf i ∈ groupedPieces) ∧
        (∀ G, G ∈ groupedPieces → ∃ i, i ∈ s ∧ groupOf i = G) ∧
        (∀ G ∈ groupedPieces, G.Nonempty ∧ IsConnected G ∧ G ⊆ K) ∧
        (∀ i, i ∈ s → piece i ⊆ groupOf i) := by sorry
