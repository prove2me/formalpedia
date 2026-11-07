-- Prove2me | Theorems.Thm_DynEdgeOrient_exists_alpha_orientation
-- name    : DynEdgeOrient.exists_alpha_orientation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:50.511433+00:00
-- url     : https://prove2.me/theorems/92576268-2743-4db1-872d-35d1b40b5e77
-- title:
--   §1, p.1: a graph of arboricity at most $\alpha$ has an $\alpha$-orientation
-- statement:
--   Let $F$ be a loop-free multigraph on a finite vertex set with arboricity at most $\alpha$, i.e. $|E(S)|\le\alpha(|S|-1)$ for every vertex set $S$. Then $F$ has an $\alpha$-orientation: an orientation of its edges in which every vertex has out-degree at most $\alpha$.
--
--   The paper derives it from the forest decomposition of Nash-Williams [42] (orient each tree of each forest toward a root). The proof of Theorem 1.2 uses it to orient the part of the graph outside each interval's vertex set.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α → |E(S)| ≤ α(|S| − 1) for every vertex set S, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - generalization: G has arboricity α → arboricity at most α; reason: a graph of arboricity exactly α is an instance
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), §1, p.1 (pdf p.2), unnumbered

import Mathlib
import Definitions.Def_DynEdgeOrient_Orientation

namespace DynEdgeOrient

/-- **An arboricity-`α` graph has an `α`-orientation** (Hiken–Wein, STOC 2027 submission,
manuscript sha256 626b4eee…, §1, p.1, unnumbered; the paper cites the forest decomposition of
Nash-Williams [42]): "If G has arboricity α, then it permits an α-orientation."

For every loop-free multigraph `F` on a finite vertex type with `|E(S)| ≤ α(|S| − 1)` for every
vertex set `S`, there is an orientation in which every vertex has out-degree at most `α`.

**Formalization Note.** The multigraph is the label set `F` with endpoint map `ends`; arboricity
`≤ α` is `ArboricityLE`, the density form of the paper's definition on p.1. -/
theorem exists_alpha_orientation {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → V × V) (hends : ∀ e, (ends e).1 ≠ (ends e).2) (F : Finset E) (α : ℕ)
    (harb : ArboricityLE ends F α) :
    ∃ σ : E → Bool, ∀ v, outDeg ends F σ v ≤ α := by sorry

end DynEdgeOrient
