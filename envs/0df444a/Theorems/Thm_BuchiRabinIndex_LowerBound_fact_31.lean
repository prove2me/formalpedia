-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_fact_31
-- name    : BuchiRabinIndex.LowerBound.fact_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:51.993635+00:00
-- url     : https://prove2.me/theorems/7dc989c1-3fd7-4fd5-b2fc-1652869be01e
-- title:
--   Fact 31 — cycles
-- statement:
--   Fix $n\ge1$. For a set $D$ of history-automaton transitions,
--   $$D\text{ is a cycle}\quad\Longleftrightarrow\quad \exists\alpha,\rho:\ \rho\text{ is an infinite history trace of }\alpha,\ \operatorname{Inf}(\rho)=D,$$
--   where the last Inf is taken on the transition triples of the trace.
--
--   For any nonempty finite list of closed walks $W_1,\ldots,W_k$, if every $W_{j+1}$ visits a history visited by an earlier walk, their union of transition sets is a cycle.
--
--   A closed walk has positive length and a reachable start. The trace in the equivalence never dies. These statements connect finite cycle witnesses with infinite-word acceptance.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: closed walks W_1,...,W_k in the union statement → a finite family indexed by Fin k with 0<k; reason: an empty family has no closed walk and is outside the stated union-of-walks construction
--   - encoding: sets of actual history-tree transitions → sets in the ambient carrier of history/letter/history triples, with actual successors enforced in traces and cycles; reason: nonactual triples never occur in a trace or cycle; source transition sets embed unchanged
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Fact 31, p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, fact 31; statement only. -/
theorem fact_31 (n : ℕ) (hn : 1 ≤ n) :
    (∀ D : Set (Edge (Fin n) (Letter n)),
      Cycle (fullBuchi n hn) D ↔
      ∃ α ρ, IsTrace (fullBuchi n hn) α ρ ∧ infSet (edgeSequence α ρ) = D) ∧
    (∀ k (H : Fin k → History (Fin n)) (v : Fin k → List (Letter n)),
      0 < k →
      (∀ i, ClosedWalk (fullBuchi n hn) (H i) (v i)) →
      (∀ j : Fin k, 0 < j.val → ∃ i : Fin k, i.val < j.val ∧
        (visited (fullBuchi n hn) (H i) (v i) ∩
          visited (fullBuchi n hn) (H j) (v j)).Nonempty) →
      Cycle (fullBuchi n hn) (⋃ i, wordEdges (fullBuchi n hn) (some (H i)) (v i))) := by sorry

end BuchiRabinIndex.LowerBound
