-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_39
-- name    : BuchiRabinIndex.LowerBound.lemma_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:27.731333+00:00
-- url     : https://prove2.me/theorems/a900c9bd-19a0-4447-ac09-f50094346558
-- title:
--   Lemma 39 — reachability
-- statement:
--   For every $n\ge1$ and every nonempty ordered tree $T$ with $|T|\le n$,
--   $$H(T)\text{ is reachable in }RT(F_n).$$
--   Here the preorder enumeration assigns own state $q_i$ to its $i$th node. Reachability means some finite word, starting in the actual initial history, has a defined trace ending in this computed canonical history. The conclusion also asserts that $H(T)$ is a valid history, rather than assuming it.
--
--   The empty prefix-closed set does not define a rooted history; the nonempty guard makes the source’s use of $H(T)$ well-defined without adding a sink or a distinguished replacement history.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: H(T) for an ordered tree T → nonempty T with H(T) represented by an optional validity-checked constructor; reason: the empty prefix-closed set does not define a rooted history; the conclusion asserts that the constructor succeeds
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 39, p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 39; statement only. -/
theorem lemma_39 (n : ℕ) (hn : 1 ≤ n) (T : Finset Node)
    (hT : Ordered T) (hne : T.Nonempty) (hcard : T.card ≤ n) :
    ∃ H, Htree n T = some H ∧ Reachable (fullBuchi n hn) H := by sorry

end BuchiRabinIndex.LowerBound
