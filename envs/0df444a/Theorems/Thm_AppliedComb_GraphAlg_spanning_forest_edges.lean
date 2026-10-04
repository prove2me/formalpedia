-- Prove2me | Theorems.Thm_AppliedComb_GraphAlg_spanning_forest_edges
-- name    : AppliedComb.GraphAlg.spanning_forest_edges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:33:46.218283+00:00
-- url     : https://prove2.me/theorems/2f634336-bf87-4e51-8447-e2e81649f04e
-- title:
--   Proposition 12.3 — edges and components of a spanning forest
-- statement:
--   Let $G = (V, E)$ be a graph on $n \ge 1$ vertices and let $H = (V, S)$ be a spanning forest of $G$. Then
--   $$0 \le |S| \le n - 1,$$
--   if $|S| = n - k$ then $H$ has exactly $k$ connected components, and in particular $H$ is a spanning tree of $G$ if and only if $|S| = n - 1$.
--
--   This is the counting fact behind both minimum spanning tree algorithms of the chapter: a spanning forest grows into a spanning tree exactly when it reaches $n - 1$ edges.
--
--   **Formalization Note.** $n$ is `Fintype.card V`, $|S|$ is `Nat.card H.edgeSet`, and the number of components is `Nat.card H.ConnectedComponent`. The hypothesis $|S| = n - k$ is written $|S| + k = n$ to avoid truncated subtraction in $\mathbb{N}$; the lower bound $0 \le |S|$ is automatic. The book's $n - 1$ upper bound presupposes $n \ge 1$, which is the hypothesis `0 < n`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 240, Proposition 12.3

import Mathlib
import Definitions.Def_AppliedComb_GraphAlg_SpanningTree

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 240, Proposition 12.3. Let `G = (V, E)` be a graph on `n` vertices and
`H = (V, S)` a spanning forest. Then `0 ≤ |S| ≤ n − 1`; if `|S| = n − k` then `H` has `k`
components; in particular `H` is a spanning tree iff it has `n − 1` edges. `|S| = n − k` is
written `|S| + k = n` (no truncated subtraction); `n ≥ 1` as the bound `|S| ≤ n − 1` requires. -/
theorem spanning_forest_edges {V : Type*} [Fintype V] (G H : SimpleGraph V) (n : ℕ)
    (hn : Fintype.card V = n) (hpos : 0 < n) (hH : IsSpanningForest G H) :
    Nat.card H.edgeSet ≤ n - 1 ∧
      (∀ k : ℕ, Nat.card H.edgeSet + k = n → Nat.card H.ConnectedComponent = k) ∧
      (IsSpanningTree G H ↔ Nat.card H.edgeSet = n - 1) := by sorry

end AppliedComb.GraphAlg
