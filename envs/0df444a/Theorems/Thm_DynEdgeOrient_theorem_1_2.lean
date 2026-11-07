-- Prove2me | Theorems.Thm_DynEdgeOrient_theorem_1_2
-- name    : DynEdgeOrient.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:32.985687+00:00
-- url     : https://prove2.me/theorems/6eb009ce-17c8-4157-9720-9b8086007079
-- title:
--   Theorem 1.2: $(5\alpha-2)$-orientations of a dynamic arboricity-$\alpha$ graph with $O(|U|\cdot\alpha\log\log n)$ edge flips
-- statement:
--   Let $G$ be a loop-free multigraph on $n$ vertices undergoing an arboricity $\alpha$-preserving sequence $U$ of edge insertions and deletions, beginning with the empty graph, and let $G_i$ be its state after the $i$-th update. There is an absolute constant $C$ such that, for every such $G$, there are orientations $\vec G_0,\dots,\vec G_{|U|}$ of $G_0,\dots,G_{|U|}$, each a $(5\alpha-2)$-orientation (every vertex has out-degree at most $5\alpha-2$), whose total number of edge flips satisfies
--
--   $$
--   \sum_{i=0}^{|U|-1}\#\{e\in G_i\cap G_{i+1}:\ e \text{ has different directions in }\vec G_i,\vec G_{i+1}\}\ \le\ C\,|U|\,\alpha\,\log_2\log_2 n .
--   $$
--
--   A newly inserted edge may be given either direction without counting as a flip.
--
--   Combined with Brodal and Fagerberg's competitiveness lemma (Lemma 1.1), the theorem shows that their algorithm maintains an $O(\alpha)$-orientation in $O(\alpha\log\log n)$ amortized time, the first improvement over $O(\alpha+\log n)$ since 1999.
--
--   **Formalization Note** The logarithm is base 2, with Lean's $\log x=0$ for $x\le 1$ handled by $\log 0=0$; for $n\le2$ the right side is $0$, and then the paper's setting needs no flips (at most $\alpha$ parallel edges between the two vertices, all oriented from one of them).
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - generalization: a sequence of multigraphs → a sequence of finite sets of labels, for every label type E and every labelling; reason: a dynamic multigraph with given edge identities is one instance; flips are counted per edge, so the identities are part of the paper's data as well
--   - encoding: flips undergone by G⃗_0, …, G⃗_{|U|} → Σ_{i<m} #{e ∈ G_i ∩ G_{i+1} : σ_i e ≠ σ_{i+1} e}; reason: an inserted edge has no previous direction, and a deleted edge no next one (Lemma 1.1 counts flips the same way)
--   - encoding: arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α → |E(S)| ≤ α(|S| − 1) for every vertex set S, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: 5α − 2 → 5 * α - 2 in ℕ; reason: equal for α ≥ 1; at α = 0 arboricity 0 forbids every edge, so no update exists and the statements are vacuous, and the paper never considers α = 0
--   - reading: O(|U| · α log log n) → ≤ C·|U|·α·log₂log₂ n with one absolute C chosen before V, E, α, |U| and G, for every n; reason: the O shows its dependence on α, so C may not depend on α; the literal form for every n is at least as strong as the asymptotic one, and the base of the logarithm changes only C; it changes the n ≤ 2 instances (bound 0, met by orienting every edge from one fixed vertex), so it is the stronger of the two readings of the O, not a convention
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Theorem 1.2, p.3 (pdf p.4); restated pp.4 and 22

import Mathlib
import Definitions.Def_DynEdgeOrient_DynamicGraph
import Definitions.Def_DynEdgeOrient_Orientation

namespace DynEdgeOrient

/-- **Theorem 1.2** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Theorem 1.2,
p.3). Let `G` be a graph on `n` nodes undergoing an arboricity-`α`-preserving sequence `U` of edge
insertions and deletions, beginning with the empty graph. There is a sequence of
`(5α − 2)`-orientations `G⃗_0, …, G⃗_{|U|}` that undergoes at most `O(|U| · α log log n)` edge flips
in total.

**Formalization Note.**
* The graph is a loop-free multigraph: edge labels `E` with endpoints `ends`, `n = |V|`; the states
  are `G 0 = ∅, G 1, …, G m` with `m = |U|`, one edge inserted or deleted per step, arboricity
  `≤ α` at every step.
* The orientations are `σ i`, one per time; `σ i` is a `(5α − 2)`-orientation of `G i`. Flips
  between `σ i` and `σ (i+1)` count only edges present in both `G i` and `G (i+1)`; a newly
  inserted edge's direction is free.
* `5α − 2` is in `ℕ`. At `α = 0` every state is edgeless, so `m = 0`.
* `O(·)` is one absolute constant `C`, chosen before `V`, `E`, `α`, `m` and `G`. The bound uses the
  literal `log₂ log₂ n` for every `n`, with Lean's `log 0 = 0` (so the right side is `0` for
  `n ≤ 2`). -/
theorem theorem_1_2 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (α m : ℕ) (G : ℕ → Finset E),
      G 0 = ∅ → IsDynamic G m → ArbPreserving ends G m α →
      ∃ σ : ℕ → E → Bool,
        (∀ i ≤ m, ∀ v, outDeg ends (G i) (σ i) v ≤ 5 * α - 2) ∧
        ((∑ i ∈ Finset.range m, flips (G i) (G (i + 1)) (σ i) (σ (i + 1)) : ℕ) : ℝ) ≤
          C * m * α * Real.logb 2 (Real.logb 2 (Fintype.card V)) := by sorry

end DynEdgeOrient
