-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_9
-- name    : BuchiRabinIndex.LowerBound.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:45.331829+00:00
-- url     : https://prove2.me/theorems/4fd8e338-cb51-4a95-8fee-f28449a7db20
-- title:
--   Lemma 9 — Schewe's acceptance criterion
-- statement:
--   Let $B$ be any nondeterministic Büchi automaton with finite nonempty state set $Q$ and finite alphabet $\Sigma$, and let $\alpha:\mathbb N\to\Sigma$. Then
--   $$\alpha\in L(B)\quad\Longleftrightarrow\quad \exists\rho,\tau:\ \rho\text{ is the infinite history trace of }\alpha,\ \tau\text{ is eventually always stable and infinitely often accepting}.$$
--   Here stability means absence from the unstable annotation at every sufficiently late transition; infinite acceptance means presence in the accepting annotation arbitrarily late.
--
--   This is Schewe’s criterion quoted as Lemma 9 in the submission. It is stated for every NBW, including empty initial or accepting sets, rather than only the full automata. Its language side is independently defined by Büchi runs.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - reading: step 4 calls nodes whose descendants are deleted accepting → only the topmost resetting nodes survive to receive accepting annotations; reason: a nested reset below one of these nodes is deleted and any old such node is unstable
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 9, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 9; statement only. -/
theorem lemma_9 {Q Sigma : Type} [Fintype Q] [Nonempty Q] [Fintype Sigma]
    (B : NBW Q Sigma) (α : ℕ → Sigma) :
    α ∈ language B ↔ ∃ (ρ : ℕ → History Q) (x : Node),
      Positive x ∧ IsTrace B α ρ ∧
      (∃ N, ∀ i ≥ N, x ∉ unstable B (ρ i) (α i)) ∧
      (∀ N, ∃ i ≥ N, x ∈ acceptingNodes B (ρ i) (α i)) := by sorry

end BuchiRabinIndex.LowerBound
