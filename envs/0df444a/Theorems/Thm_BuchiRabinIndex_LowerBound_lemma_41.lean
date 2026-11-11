-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_41
-- name    : BuchiRabinIndex.LowerBound.lemma_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:33.045116+00:00
-- url     : https://prove2.me/theorems/54ff4681-873b-48e4-8c22-8ea5c9bca639
-- title:
--   Lemma 41 — sandwiched rejecting cycle
-- statement:
--   Let $n\ge1$, let $S$ be a clique of $G_n$, and take distinct $x,y\in S$. For the constructed witness cycles $C_x,C_y$, there exists a rejecting cycle $D$ such that
--   $$C_y\subseteq D\subseteq C_x\cup C_y\quad\text{or}\quad C_x\subseteq D\subseteq C_x\cup C_y.$$
--   Rejecting means every infinite realization of $D$ spells a word outside the run-defined $L(F_n)$, and the conclusion also requires $D$ to be a genuine cycle.
--
--   The witnesses $C_x,C_y$ are the concrete cycles of §6.3, not arbitrary accepting cycles supplied as independent parameters.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
--   - encoding: sets of actual history-tree transitions → sets in the ambient carrier of history/letter/history triples, with actual successors enforced in traces and cycles; reason: nonactual triples never occur in a trace or cycle; source transition sets embed unchanged
--   - encoding: the canonical histories H(T) used by the witness construction → the optional validity-checked Htree constructor, used at the specified chain and union trees; reason: the clique hypotheses ensure these trees are nonempty, ordered and have at most n nodes; Lemma 40 explicitly concludes constructor success, and no replacement history is introduced
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 41, p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 41; statement only. -/
theorem lemma_41 (n : ℕ) (hn : 1 ≤ n) (S : Finset Node)
    (hS : S ⊆ fullTree n) (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y)
    (x y : Node) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    ∃ D, RejectingCycle (fullBuchi n hn) D ∧
      ((Ccycle n hn S y ⊆ D ∧ D ⊆ Ccycle n hn S x ∪ Ccycle n hn S y) ∨
       (Ccycle n hn S x ⊆ D ∧ D ⊆ Ccycle n hn S x ∪ Ccycle n hn S y)) := by sorry

end BuchiRabinIndex.LowerBound
