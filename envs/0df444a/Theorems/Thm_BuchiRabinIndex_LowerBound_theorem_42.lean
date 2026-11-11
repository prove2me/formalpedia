-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_theorem_42
-- name    : BuchiRabinIndex.LowerBound.theorem_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:42.637878+00:00
-- url     : https://prove2.me/theorems/c13c55eb-f61b-455b-acc3-4ceb2d867ac1
-- title:
--   Theorem 42 — index lower bound for every Rabin condition
-- statement:
--   For every integer $n\ge1$, let $F_n$ be the full Büchi automaton and keep the history-tree transition structure $RT(F_n)$ fixed. Every finite correct transition-based Rabin condition $\lambda'$ satisfies
--   $$|\lambda'|\ge\omega(G_n),\qquad |\lambda'|\ge2^{n/2}\ \text{if }n\text{ is even},\qquad |\lambda'|\ge3\cdot2^{(n-3)/2}\ \text{if }n\ge3\text{ is odd}.$$
--   The same three inequalities hold for every finite correct state-based Rabin condition on that history-tree automaton.
--
--   Correctness means exact equality of the accepted language with $L(F_n)$, independently defined by Büchi runs. Pair components may be arbitrary sets; the condition need not come from merging Schewe’s pairs and is not restricted to reachable transitions. The $\omega(G_n)$ clause includes $n=1$. All explicit bounds and both acceptance conventions are part of this one goal.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
--   - encoding: a finite set of Rabin pairs on transitions or states → Finset of pairs of arbitrary sets; reason: cardinality counts distinct pairs and all source conditions are expressible
--   - generalization: finite Rabin conditions whose components are sets of actual transitions → finite Rabin conditions whose components may also contain nonactual history/letter/history triples; reason: traces use actual successors only; restricting every component to actual transitions preserves the accepted language and cannot increase the number of distinct pairs, so the source bound implies this extension and every source condition is included
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Theorem 42, p. 29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, theorem 42; statement only. -/
theorem theorem_42 (n : ℕ) (hn : 1 ≤ n) :
    (∀ r : RabinCondition (Edge (Fin n) (Letter n)),
      CorrectTransition (fullBuchi n hn) r →
      omega n ≤ r.card ∧ (Even n → 2 ^ (n / 2) ≤ r.card) ∧
        (Odd n → 3 ≤ n → 3 * 2 ^ ((n - 3) / 2) ≤ r.card)) ∧
    (∀ r : RabinCondition (History (Fin n)),
      CorrectState (fullBuchi n hn) r →
      omega n ≤ r.card ∧ (Even n → 2 ^ (n / 2) ≤ r.card) ∧
        (Odd n → 3 ≤ n → 3 * 2 ^ ((n - 3) / 2) ≤ r.card)) := by sorry

end BuchiRabinIndex.LowerBound
