-- Prove2me | Theorems.Thm_AppliedComb_GraphAlg_exchange_principle
-- name    : AppliedComb.GraphAlg.exchange_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:34:59.258798+00:00
-- url     : https://prove2.me/theorems/8147cfe8-0123-4faa-9350-8deb3b0297c2
-- title:
--   Proposition 12.4 — the exchange principle for spanning trees
-- statement:
--   Let $T = (V, S)$ be a spanning tree of a finite graph $G$ and let $e = xy$ be an edge of $G$ that is not an edge of $T$. Then:
--
--   1. there is a unique path $P = (x_0, x_1, \dots, x_t)$ in $T$ with $x_0 = x$, $x_t = y$ and $x_i x_{i+1} \in S$ for $i = 0, \dots, t-1$;
--   2. for each $i = 0, 1, \dots, t - 1$, with $f_i = x_i x_{i+1}$, the graph $T_i = (V, S_i)$, where
--   $$S_i = \{e\} \cup \{g \in S : g \ne f_i\},$$
--   is a spanning tree of $G$.
--
--   Exchanging one tree edge on the path for the non-tree edge $e$ is the step used to compare spanning trees of different weights (Lemma 12.6).
--
--   **Formalization Note.** A path is a Mathlib walk `P : T.Walk x y` with `P.IsPath` (distinct vertices); $t$ is `P.length` and $x_i$ is `P.getVert i`. Part 1 is `∃! P, P.IsPath`. In part 2 the statement is made for every path from $x$ to $y$ in $T$ (by part 1 there is exactly one), and $T_i$ is `SimpleGraph.fromEdgeSet` of the edge set $\{e\} \cup \{g \in S : g \ne f_i\}$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 241, Proposition 12.4 (Exchange Principle)

import Mathlib
import Definitions.Def_AppliedComb_GraphAlg_SpanningTree

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 241, Proposition 12.4 (Exchange Principle). Let `T = (V, S)` be a spanning
tree in a graph `G` and `e = xy` an edge of `G` not in `T`. Then (1) there is a unique path
`P = (x₀, …, x_t)` in `T` from `x = x₀` to `y = x_t`, and (2) for each `i = 0, …, t − 1`, with
`fᵢ = xᵢxᵢ₊₁`, the graph `Tᵢ = (V, Sᵢ)` with `Sᵢ = {e} ∪ {g ∈ S : g ≠ fᵢ}` is a spanning tree of
`G`. Paths are Mathlib walks with distinct vertices; `t` is the walk's length and `xᵢ` its
`i`-th vertex. -/
theorem exchange_principle {V : Type*} [Fintype V] (G T : SimpleGraph V)
    (hT : IsSpanningTree G T) (x y : V) (he : G.Adj x y) (heT : ¬ T.Adj x y) :
    (∃! P : T.Walk x y, P.IsPath) ∧
      ∀ P : T.Walk x y, P.IsPath → ∀ i : ℕ, i < P.length →
        IsSpanningTree G (SimpleGraph.fromEdgeSet
          (insert s(x, y) {g ∈ T.edgeSet | g ≠ s(P.getVert i, P.getVert (i + 1))})) := by sorry

end AppliedComb.GraphAlg
