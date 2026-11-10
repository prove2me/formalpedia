-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_cut_or_cluster
-- name    : FlowOptimalSeparators.MinorFree.cut_or_cluster
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:09:04.523584+00:00
-- url     : https://prove2.me/theorems/b2deb68b-409c-450b-bb4a-b0d05a76becb
-- title:
--   Theorem 7 — cut or cluster with SSSP-relative expected time
-- statement:
--   Let $h\ge2$, let $G$ exclude the once-subdivided $K_h$ as an induced minor, let $w(v)\ge1$ be integer vertex weights, set $W=\sum_vw(v)$, and let $D$ be any real number with $0<D\le n$. One randomized program returns either a set $K$ with
--   $$|K|>3n/4,\qquad \forall u,v\in K\ \exists P\subseteq G[K]:w(P)\le D,$$
--   or a balanced separator satisfying
--   $$|S|\le C_{\rm size}\frac{W\ln(hW/n)}{D}.$$
--   Its expected scalar instruction count is at most
--   $$C_{\rm time}h^5\bigl(T_{\rm SSSP}(n+1,m+n,2W)+m+n\bigr).$$
--   The constants and main code precede both the shortest-path routine and every graph input. The statement holds for every correct integral shortest-path block having finite actual worst time; every completed call obeys the stated size and distance limits. Size and cluster correctness hold for every returned output, and expected total work is finite.
--
--   The main code and resource constants are independent of the chosen correct SSSP routine. The routine preserves caller register 0 and memory beyond its reserved scratch prefix; distance limits are not supplied as input.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: an algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws; reason: the paper does not specify a bit machine; the chunk brief fixes the arithmetic RAM reading, without graph or shortest-path oracles
--   - encoding: expected running time of a randomized algorithm → independent product-uniform tapes, every returned output correct, almost-sure termination, measurable extended work with finite expectation; reason: divergent runs cost infinity and cannot disappear through a total real integral
--   - encoding: TSSSP is the time of an actual integer shortest-path algorithm → the extended supremum of the fixed correct code block’s executed instruction counts, finite for every finite limit; reason: the runtime interface is computed from code semantics and cannot be assigned an arbitrary number
--   - encoding: shortest-path computations and time relative to an SSSP implementation → one main code block with uniform guarantees for every correct SSSP routine satisfying the declared memory convention; reason: the reduction cannot choose a routine that performs unrelated work excluded from the additional-time count or inflates its own TSSSP; calls execute actual instructions and only the specified answers and preserved caller data may be relied on
--   - encoding: a shortest-path subroutine used in the running-time reduction → a deterministic routine preserving register 0 and both memories outside its reserved scratch prefix, with distance limits used only in analysis; reason: a caller/callee memory convention permits composition without supplying diameter advice; standard array implementations fit the fixed scratch allowance
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 14, 22–25, Theorem 7; Algorithm 3

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_AlgorithmOutputs

open scoped ENNReal
set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Theorem 7, p.14 (proved pp.24-25). TSSSP is the actual worst time of the fixed,
correct integer SSSP code, not an arbitrary supplied number. The main code and constants
are uniform over every such routine. D ranges over all reals in (0,n]. -/
theorem cut_or_cluster :
    ∃ (Csize Ctime : ℝ) (main : List Instruction),
      0 < Csize ∧ 0 < Ctime ∧
      ∀ (ss : List Instruction), SSSPCorrect ss true →
      (∀ N M L, TSSSP ss N M L ≠ ⊤) →
      ∀ (n h : ℕ) (G : Graph n) (A : AdjacencyInput G) (w : Fin n → ℕ) (D : ℝ),
        2 ≤ h → InducedSubdivisionFree G h → (∀ v, 1 ≤ w v) → 0 < D → D ≤ n →
        let W := ∑ v, w v
        let P : Program := ⟨main, ss⟩
        let ns := A.encode h ++ (List.finRange n).map w
        let rs := [D]
        RunsWith P ns rs (CutOrClusterOutput G w h D Csize)
          (Ctime * (h : ℝ) ^ 5 *
            ((TSSSP ss (n + 1) (edgeCount G + n) (2 * W)).toReal + edgeCount G + n)) ∧
        CallsSatisfy P ns rs
          (IsShortestCall (n + 1) (edgeCount G + n) (2 * W) true) := by sorry

end FlowOptimalSeparators.MinorFree
