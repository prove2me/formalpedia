-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_minor_free_separator_algorithm
-- name    : FlowOptimalSeparators.MinorFree.minor_free_separator_algorithm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:08:03.471354+00:00
-- url     : https://prove2.me/theorems/9f928cb2-0c56-4297-84d3-59f07c4a01f6
-- title:
--   Theorem 2 — flow-optimal balanced minor-free separators
-- statement:
--   There are absolute constants $C_{\rm size},C_{\rm time}>0$ and one fixed randomized scalar RAM program such that for every finite $K_h$-minor-free graph $G$, with $n$ vertices and $m$ edges, it returns a vertex set $S$ satisfying
--   $$4|K|\le3n\quad(K\text{ a component of }G-S),\qquad
--   |S|\le C_{\rm size}h\ln h\sqrt n,$$
--   and
--   $$\mathbb E[\operatorname{work}]\le C_{\rm time}h^7(m+n)<\infty.$$
--   The component condition means that every component obeys the bound, including when there are no components. Output and size correctness hold on every terminating execution and termination is almost sure. Every adjacency-list ordering is allowed. There is no connectedness, positive-edge-count, embedding, or supplied minor-free certificate assumption. The empty graph and $h=1,2$ are included; the excluded empty clique makes $h=0$ vacuous. Polynomial index-word ranges are uniform over all inputs.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: an algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws; reason: the paper does not specify a bit machine; the chunk brief fixes the arithmetic RAM reading, without graph or shortest-path oracles
--   - encoding: expected running time of a randomized algorithm → independent product-uniform tapes, every returned output correct, almost-sure termination, measurable extended work with finite expectation; reason: divergent runs cost infinity and cannot disappear through a total real integral
--   - encoding: arbitrary h and graph sizes, with asymptotic size and time bounds → all n,h, natural logarithms, an immediate zero-work empty-input convention and a uniform polynomial range for natural index words; reason: small and edgeless instances are handled by program branches; changing a fixed logarithm base only changes a universal constant
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 3, 17, Theorem 2

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_SeparatorOutput

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Theorem 2, pp.3,17: one finite program and positive absolute constants before all inputs.
Correctness and separator size hold on every returned execution. Infinite executions have
infinite work; the extended expected work is finite. Neither a minor test nor any graph
operation is a machine primitive. Arbitrary adjacency-list orders and disconnected inputs
are allowed, including the empty graph and h=1,2. -/
theorem minor_free_separator_algorithm :
    ∃ (Csize Ctime : ℝ) (P : Program) (k : ℕ), 0 < Csize ∧ 0 < Ctime ∧
      ∀ (n h : ℕ) (G : Graph n) (A : AdjacencyInput G), ExcludesClique G h →
        RunsWith P (A.encode h) [] (SeparatorOutput G h Csize)
          (Ctime * (h : ℝ) ^ 7 * (edgeCount G + n)) ∧
        IndexRange P (A.encode h) [] (30001 * (2 + n + h) ^ (k + 1)) := by sorry

end FlowOptimalSeparators.MinorFree
