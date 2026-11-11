-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_32
-- name    : BuchiRabinIndex.LowerBound.lemma_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:43.791978+00:00
-- url     : https://prove2.me/theorems/ce4e3a81-4f76-46dd-9746-f7c51e32085e
-- title:
--   Lemma 32 — accepting cycles
-- statement:
--   Fix $n\ge1$ and a cycle $D$ of $RT(F_n)$. Then
--   $$D\text{ is accepting}\quad\Longleftrightarrow\quad \exists\tau:\ (\forall e\in D,\ \tau\text{ is stable at }e)\ \land\ (\exists e\in D,\ \tau\text{ is accepting at }e).$$
--   An accepting cycle means that every infinite trace with recurring transition set $D$ spells a word of $L(F_n)$. Cyclehood is an explicit hypothesis, so the universal language condition is not being used on an unrealizable transition set.
--
--   This retains both directions of the source’s acceptance criterion.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: sets of actual history-tree transitions → sets in the ambient carrier of history/letter/history triples, with actual successors enforced in traces and cycles; reason: nonactual triples never occur in a trace or cycle; source transition sets embed unchanged
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 32, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 32; statement only. -/
theorem lemma_32 (n : ℕ) (hn : 1 ≤ n) (D : Set (Edge (Fin n) (Letter n)))
    (hD : Cycle (fullBuchi n hn) D) :
    AcceptingCycle (fullBuchi n hn) D ↔
    ∃ x : Node, Positive x ∧
      (∀ e ∈ D, x ∉ unst (fullBuchi n hn) e) ∧
      (∃ e ∈ D, x ∈ acc (fullBuchi n hn) e) := by sorry

end BuchiRabinIndex.LowerBound
