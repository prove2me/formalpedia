-- Prove2me | Theorems.Thm_BergeMatching_Core_theorem_1
-- name    : BergeMatching.Core.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:07:34.982957+00:00
-- url     : https://prove2.me/theorems/e900ee8c-afdf-47d5-a124-7e6d8390c8e3
-- title:
--   Theorem 1 — a matching is maximum iff no alternating chain connects two neutral points
-- statement:
--   Let $G = (X, U)$ be a finite simple graph and $V \subseteq U$ a matching. Call the edges of $V$ strong and the other edges weak; a vertex met by no strong edge is **neutral**, and an **alternating chain** is a walk that does not use the same edge twice and in which, of any two consecutive edges, one is strong and the other weak. Then
--   $$
--   V \text{ is a maximum matching} \iff \text{no alternating chain connects a neutral point } a \text{ to a neutral point } a' \neq a .
--   $$
--   Here "maximum" means that no matching of $G$ has more edges than $V$.
--
--   This is Berge's characterization of maximum matchings by augmenting chains. It turns the global optimality of a matching into a local, checkable condition, and it is the basis of the augmenting-path algorithms for maximum matching in general graphs, notably Edmonds' blossom algorithm.
--
--   **Formalization Note** The graph is a finite Mathlib `SimpleGraph`, the matching is a subgraph with `IsMatching`, and its size is the number of its edges. Alternating chains are trails (no repeated edge; vertices may repeat), and alternation is required of consecutive edges only. The endpoints are required to be distinct, as in the paper's proof ("a neutral point $a'$ different from $a$"); otherwise the one-vertex chain at any neutral point would count. No connectedness or nonemptiness hypothesis is assumed.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, Theorem 1

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Theorem 1: a matching is maximum if and only if there does not exist
an alternating chain connecting a neutral point to another neutral point. -/
theorem theorem_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) :
    IsMaximumMatching M ↔
      ¬ ∃ (a a' : V) (p : G.Walk a a'),
          a ≠ a' ∧ IsNeutral M a ∧ IsNeutral M a' ∧ IsAlternatingChain M p := by sorry

end BergeMatching.Core
