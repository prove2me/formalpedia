-- Prove2me | Theorems.Thm_BunkbedFalse_bunkbed_conjecture_false
-- name    : BunkbedFalse.bunkbed_conjecture_false
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:59:40.045419+00:00
-- url     : https://prove2.me/theorems/6619f63b-95ee-4233-8741-8f51852d2990
-- title:
--   The bunkbed conjecture is false
-- statement:
--   **The bunkbed conjecture is false.**
--
--   Kasteleyn's bunkbed conjecture (1985) asserts that for every finite connected graph $G = (V,E)$, every set $T \subseteq V$ of transversal vertices, every retention probability $0 < p < 1$ and all $u, v \in V$,
--
--   $$\mathbb{P}^{\mathrm{bb}}_p\bigl[u \leftrightarrow v\bigr] \;\ge\; \mathbb{P}^{\mathrm{bb}}_p\bigl[u \leftrightarrow v'\bigr],$$
--
--   where percolation is performed independently on the two levels of the bunkbed graph, all posts above $T$ are retained, and $v'$ denotes the counterpart of $v$ in the opposite level. In words: staying on your own level is at least as good as crossing over.
--
--   The goal of this mission is to prove that this is **not** true — the negation of the statement above, which is exactly the "In particular, the BBC is false" of Theorem 1.2 of Gladkov, Pak and Zimin.
--
--   A counterexample must be exhibited; the conjecture holds in many special cases (wheels, complete graphs, complete bipartite graphs, graphs with an automorphism exchanging $u$ and $v$, at most two transversal vertices, and in the $p \uparrow 1$ limit), so no general argument can work. The route laid out by the milestones follows the source: Hollom's hypergraph violates the analogous inequality; a robust version of that violation survives in the Wierman–Ziff model; a gadget graph simulates a hyperedge well enough to inherit it; and substituting the gadget into Hollom's hypergraph produces an explicit finite graph.
--
--   **Formalization Note** The conjecture is stated as a `Prop` quantifying over all finite vertex types, edge sets, transversal sets and rational $0 < p < 1$, and the goal is its negation. Proving it requires only exhibiting one counterexample, so the goal follows immediately from the explicit-counterexample milestone; the mathematical work lies entirely in the milestones.
--
--   **On the rational parameter.** The conjecture is stated here for rational $p$ with $0 < p < 1$. This makes the refutation *no weaker* than the real-parameter version: the real-parameter conjecture implies the rational one, so negating the rational one implies negating the real one. The counterexample occurs at $p = 1/2$, which is rational, so nothing is lost. Likewise the restriction of the vertex type to `Type` costs nothing, since every finite type is equivalent to one there.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 2, the "In particular, the BBC is false." of Theorem 1.2; Conjecture 1.1 is on p. 1.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **The bunkbed conjecture is false** — the goal of this mission, and the "In particular"
of Theorem 1.2 of Gladkov–Pak–Zimin. -/
theorem bunkbed_conjecture_false : ¬ BunkbedConjecture := by sorry

end BunkbedFalse
