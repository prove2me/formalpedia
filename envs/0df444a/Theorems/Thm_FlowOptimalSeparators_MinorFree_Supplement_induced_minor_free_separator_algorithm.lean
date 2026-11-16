-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_Supplement_induced_minor_free_separator_algorithm
-- name    : FlowOptimalSeparators.MinorFree.Supplement.induced_minor_free_separator_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:03:00.070405+00:00
-- url     : https://prove2.me/theorems/e56b8ab4-d18c-4828-8fc8-6fdd81c72eb8
-- title:
--   Theorem 3 — balanced separators for induced-minor-free graphs
-- statement:
--   There are absolute constants $C_{\rm size},C_{\rm time}>0$ and one fixed randomized scalar RAM program such that for every finite graph $H$ and every finite $H$-induced-minor-free graph $G$ with $n$ vertices and $m$ edges, given $G$'s adjacency arrays together with $|V(H)|$ and $|E(H)|$, it returns a vertex set $S$ such that every connected component $K$ of $G-S$ satisfies $4|K|\le3n$, with
--   $$|S|\ \le\ C_{\rm size}\,\ln|V(H)|\,\sqrt{m\,(|V(H)|+|E(H)|)}\qquad(n\ge2),$$
--   and
--   $$\mathbb E[\operatorname{work}]\ \le\ C_{\rm time}\,|V(H)|^7\,(m+n)\ <\ \infty.$$
--   Output correctness and the size bound hold on every terminating execution, and termination is almost sure. Every adjacency-list ordering is allowed, and there is no connectedness, edge-count or certificate assumption. The separator size depends on $m$ rather than on $n$ alone, which makes it meaningful for sparse graphs such as string graphs. This is the induced-minor companion of the mission's goal, Theorem 2.
--
--   Differences from the source:
--   - encoding: finite simple graphs H and G on arbitrary vertex sets, G given as adjacency lists → SimpleGraph (Fin a) and SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders for G; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: an algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws (published RandomRAM); reason: the paper does not specify a bit machine; the arithmetic RAM reading is the one of the published Theorem 2, without graph, minor or shortest-path oracles
--   - encoding: expected running time of a randomized algorithm → independent product-uniform tapes, every returned output correct, almost-sure termination, measurable extended work with finite expectation; reason: divergent runs cost infinity and cannot disappear through a total real integral
--   - generalization: for a fixed graph H, a randomized algorithm for H-induced-minor-free G → one program and absolute constants Csize, Ctime chosen before H, G and the adjacency order; the program receives only |V(H)| and |E(H)| after G's arrays; reason: a single program uniform over H that sees only the two sizes is in particular an algorithm for each fixed H; the bounds keep their explicit dependence on |V(H)| and |E(H)| with absolute constants
--   - reading: a 3/4-balanced separator of size O(log|V(H)| √(m(|V(H)|+|E(H)|))) → the size bound for every n ≥ 2, balance for every n; reason: at n = 1 we have m = 0, so the printed bound is 0, yet the only 3/4-balanced set of a one-vertex graph is that vertex; no algorithm can meet the literal bound there
--   - encoding: asymptotic size and time bounds over arbitrary graph sizes → all n, natural logarithm, an immediate zero-work empty-input convention and a uniform polynomial range for natural index words; reason: small and edgeless instances are handled by program branches; changing a fixed logarithm base only changes a universal constant
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 3, 20, Theorem 3

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Supplement_InducedMinorFree

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree.Supplement

/-- Theorem 3, p.3 (restated and proved p.20): one finite program and positive absolute
constants before every `H`, `G` and adjacency order. Correctness and the separator size hold on
every returned execution, termination is almost sure and the extended expected work is finite.
The program sees `H` only through `|V(H)|` and `|E(H)|`; no minor test or graph operation is a
machine primitive. Disconnected, edgeless and small inputs are included. -/
theorem induced_minor_free_separator_algorithm :
    ∃ (Csize Ctime : ℝ) (P : Program) (k : ℕ), 0 < Csize ∧ 0 < Ctime ∧
      ∀ (a : ℕ) (H : Graph a) (n : ℕ) (G : Graph n) (A : AdjacencyInput G),
        InducedMinorFree H G →
        RunsWith P (inducedInput A H) [] (InducedSeparatorOutput G H Csize)
          (Ctime * (a : ℝ) ^ 7 * (edgeCount G + n)) ∧
        IndexRange P (inducedInput A H) []
          (30001 * (2 + n + a + edgeCount H) ^ (k + 1)) := by sorry

end FlowOptimalSeparators.MinorFree.Supplement
