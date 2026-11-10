-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_find_prefix
-- name    : FlowOptimalSeparators.MinorFree.find_prefix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:09:09.318078+00:00
-- url     : https://prove2.me/theorems/64ae4ce4-e6df-4621-96e9-b2cf39cb37c4
-- title:
--   Lemma 9 — randomized prefix or large ball
-- statement:
--   In the connected graph and positive edge-length setting of Section 6.1, let $h\ge2$, set $b=n/(8h^2)$, and let $Y=(y_1,\ldots,y_k)$ be any duplicate-free ordered vertex set with $|B(Y,4)|>b$. There is a randomized program returning either a centre $x$ with $|B(x,11)|>b$, or $1\le t\le k$ with
--   $$b<|B(\{y_1,\ldots,y_t\},4)|\le3b.$$
--   It uses expected $O(h^2)$ actual single-source shortest-path calls and $O(h^2(m+n))$ additional scalar operations. Both output alternatives, almost-sure termination, and the two finite expected resource bounds hold uniformly for every correct subroutine under the calling convention; $Y$ is not restricted to a DFS prefix.
--
--   The main code and resource constants are independent of the chosen correct SSSP routine. The routine preserves caller register 0 and memory beyond its reserved scratch prefix; distance limits are not supplied as input.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: a randomized algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws; reason: the paper does not specify a bit machine; the chunk brief fixes the arithmetic RAM reading, without graph or shortest-path oracles
--   - encoding: expected running time of a randomized algorithm → independent product-uniform tapes, every returned output correct, almost-sure termination, measurable extended work with finite expectation; reason: divergent runs cost infinity and cannot disappear through a total real integral
--   - encoding: single-source computations from vertex sets → calls to a fixed single-source code block on graphs with at most n+1 vertices and m+n edges; reason: the dummy-source construction in the proof is serialized by charged scalar instructions; completed calls must have correct query arrays and parent-tree outputs
--   - encoding: shortest-path computations and time relative to an SSSP implementation → one main code block with uniform guarantees for every correct SSSP routine satisfying the declared memory convention; reason: the reduction cannot choose a routine that performs unrelated work excluded from the additional-time count or inflates its own TSSSP; calls execute actual instructions and only the specified answers and preserved caller data may be relied on
--   - encoding: a shortest-path subroutine used in the running-time reduction → a deterministic routine preserving register 0 and both memories outside its reserved scratch prefix, with distance limits used only in analysis; reason: a caller/callee memory convention permits composition without supplying diameter advice; standard array implementations fit the fixed scratch allowance
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 25–26, Lemma 9; Algorithm 4

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_AlgorithmOutputs

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 9, p.25. Both outputs and both expected resource bounds refer to one finite
main program, uniformly for every correct SSSP code block under the memory convention. -/
theorem find_prefix :
    ∃ (Ccalls Cextra : ℝ) (main : List Instruction),
      0 < Ccalls ∧ 0 < Cextra ∧
      ∀ (ss : List Instruction), SSSPCorrect ss false →
      ∀ (n h : ℕ) (G : Graph n) (A : AdjacencyInput G)
        (ℓ : Fin n → Fin n → ℝ) (Y : List (Fin n)),
        2 ≤ h → G.Connected → InducedSubdivisionFree G h → ValidLengths G ℓ →
        Y.Nodup → threshold n h < ((ball G (edgeMetric ℓ) Y.toFinset 4).card : ℝ) →
        let P : Program := ⟨main, ss⟩
        let ns := A.encode h ++ [Y.length] ++ Y.map Fin.val
        let rs := edgeInput A ℓ
        Returns P ns rs (PrefixOutput G ℓ h Y) ∧
        CallsSatisfy P ns rs (IsShortestCall (n + 1) (edgeCount G + n) (n + 1) false) ∧
        ExpectedResource RAMState.calls P ns rs (Ccalls * (h : ℝ) ^ 2) ∧
        ExpectedResource RAMState.additional P ns rs
          (Cextra * (h : ℝ) ^ 2 * (edgeCount G + n)) := by sorry

end FlowOptimalSeparators.MinorFree
