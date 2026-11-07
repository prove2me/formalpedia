-- Prove2me | Theorems.Thm_DDNNFNeg_proposition_5_2_exists
-- name    : DDNNFNeg.proposition_5_2_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:47.592195+00:00
-- url     : https://prove2.me/theorems/0b33b1e4-e964-4b7b-af4a-814e71ef93d2
-- title:
--   p.12 — existence of simple 3-regular 3-edge-colourable balanced-cut $\gamma$-edge expanders (the graphs of Proposition 5.2)
-- statement:
--   There is an absolute constant $\gamma \in (0,1)$ such that for every even $n \ge 6$ there exist a simple 3-regular balanced-cut $\gamma$-edge expander $G$ on $n$ vertices and a proper 3-edge-colouring of $G$.
--
--   These are the graphs for which the lower bound of Theorem 5.3 is proved; their existence is all that Theorem 1.1 needs.
--
--   **Formalization Note** The source sentence ("The existence of such graphs may be easily established") refers to the graphs of Proposition 5.2, whose parameters ($\gamma$ absolute, all even $n \ge 6$) are stated here. Proposition 5.2's deterministic polynomial-time algorithm is not formalized in this mission.
--
--   Differences from the source:
--   - reading: “The existence of such graphs may be easily established” (such graphs: simple 3-regular 3-edge-colorable balanced-cut edge expanders) → one absolute γ ∈ (0,1) and, for every even n ≥ 6, a graph on Fin n with a proper colouring; reason: the parameters are those of Proposition 5.2, to which the sentence refers; the algorithmic clause of Proposition 5.2 is a separate statement, not formalized
--   - encoding: a simple graph on n vertices → a SimpleGraph on Fin n (with a decidable adjacency relation); reason: SimpleGraph is simple by construction; decidability is a Lean convention
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, p.12 (existence sentence before Proposition 5.2, with the parameters of Proposition 5.2)

import Mathlib
import Definitions.Def_DDNNFNeg_IsBalancedCutExpander
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring

namespace DDNNFNeg

/-- **Existence of the expanders of Proposition 5.2** (§5.2, sentence before Proposition 5.2) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.12): there is an absolute constant
`γ ∈ (0, 1)` such that for all even `n ≥ 6` there is a simple 3-regular balanced-cut
`γ`-edge expander `G` on `n` vertices together with a proper 3-edge-colouring of `G`.

**Formalization Note** The paper states that a deterministic polynomial-time algorithm outputs
such a graph on input `1ⁿ`; this item states the existence of the graphs, which is all that
Theorem 1.1 uses (the paper states existence separately on p.12). A `SimpleGraph` is simple
(no loops, no parallel edges) by construction. -/
theorem proposition_5_2_exists :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∀ n : ℕ, Even n → 6 ≤ n →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree 3 ∧
        IsBalancedCutExpander γ G ∧ ∃ c : Sym2 (Fin n) → Fin 3, IsProperEdgeColoring G c := by sorry

end DDNNFNeg
