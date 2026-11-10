-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_ball_or_pair
-- name    : FlowOptimalSeparators.MinorFree.ball_or_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:08:52.244977+00:00
-- url     : https://prove2.me/theorems/78ee7178-1773-48b4-aa56-94ef9ac8dd75
-- title:
--   Lemma 7 — ball or separated pair
-- statement:
--   Let $h\ge2$, let $G$ be a connected graph excluding the once-subdivided $K_h$ as an induced minor, and give its edges arbitrary lengths in $(0,1]$. Set $b=n/(8h^2)$. One randomized program returns either
--   $$|B(x,11)|>b,$$
--   or disjoint vertex sets satisfying
--   $$|A|\ge b,\quad |B|\ge b,\quad d(A,B)>1.$$
--   Its expected number of actual shortest-path computations is $O(h^3)$ and its expected additional scalar work is $O(h^3(m+n))$. Output correctness holds on every terminating execution, with almost-sure termination; no failure probability or integer-length restriction is introduced.
--
--   The main code and resource constants are independent of the chosen correct SSSP routine. The routine preserves caller register 0 and memory beyond its reserved scratch prefix; distance limits are not supplied as input.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: a randomized algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws; reason: the paper does not specify a bit machine; the chunk brief fixes the arithmetic RAM reading, without graph or shortest-path oracles
--   - encoding: expected running time of a randomized algorithm → independent product-uniform tapes, every returned output correct, almost-sure termination, measurable extended work with finite expectation; reason: divergent runs cost infinity and cannot disappear through a total real integral
--   - encoding: shortest paths from sets of sources → actual fixed-code single-source calls, allowing one extra dummy source and at most n extra edges; reason: this is the source proof’s multi-source reduction; the call history validates the actual inputs and outputs
--   - encoding: shortest-path computations and time relative to an SSSP implementation → one main code block with uniform guarantees for every correct SSSP routine satisfying the declared memory convention; reason: the reduction cannot choose a routine that performs unrelated work excluded from the additional-time count or inflates its own TSSSP; calls execute actual instructions and only the specified answers and preserved caller data may be relied on
--   - encoding: a shortest-path subroutine used in the running-time reduction → a deterministic routine preserving register 0 and both memories outside its reserved scratch prefix, with distance limits used only in analysis; reason: a caller/callee memory convention permits composition without supplying diameter advice; standard array implementations fit the fixed scratch allowance
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 22, 26–28, Lemma 7; Algorithm 5

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_AlgorithmOutputs

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 7, p.22. Arbitrary positive real lengths at most one; strict >1 separation,
strict >b ball size, and both expected operation and SSSP-count guarantees, uniformly
for every correct SSSP code block under the memory convention. -/
theorem ball_or_pair :
    ∃ (Ccalls Cextra : ℝ) (main : List Instruction),
      0 < Ccalls ∧ 0 < Cextra ∧
      ∀ (ss : List Instruction), SSSPCorrect ss false →
      ∀ (n h : ℕ) (G : Graph n) (A : AdjacencyInput G) (ℓ : Fin n → Fin n → ℝ),
        2 ≤ h → G.Connected → InducedSubdivisionFree G h → ValidLengths G ℓ →
        let P : Program := ⟨main, ss⟩
        Returns P (A.encode h) (edgeInput A ℓ) (BallOrPairOutput G ℓ h) ∧
        CallsSatisfy P (A.encode h) (edgeInput A ℓ)
          (IsShortestCall (n + 1) (edgeCount G + n) (n + 1) false) ∧
        ExpectedResource RAMState.calls P (A.encode h) (edgeInput A ℓ) (Ccalls * (h : ℝ) ^ 3) ∧
        ExpectedResource RAMState.additional P (A.encode h) (edgeInput A ℓ)
          (Cextra * (h : ℝ) ^ 3 * (edgeCount G + n)) := by sorry

end FlowOptimalSeparators.MinorFree
