-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_24
-- name    : BuchiRabinIndex.LowerBound.Supplement.theorem_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:53:01.581956+00:00
-- url     : https://prove2.me/theorems/3f2b3a88-7c4d-4516-bdc4-39820413b641
-- title:
--   Theorem 24 — Correctness of the reduced Rabin condition
-- statement:
--   For every nondeterministic Büchi automaton $B$ with finite nonempty state set and finite alphabet, the unchanged history-tree structure equipped with the reduced reachable Rabin condition satisfies
--   $$L(RT')=L(B).$$
--   The right side is independently defined by Büchi runs. Initial and accepting subsets may be empty, and transitions need not be total. Both directions of language equality are asserted. Only the acceptance condition is merged.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
--   - encoding: labels are defined on the tree node set → the published History subtype extends labels by the empty set outside its node set; reason: the normalized extension is unique and introduces no history states
--   - encoding: the deterministic history trace may cease when the root is deleted or its initial label is empty → published Option successor and initial history; an absent infinite trace is rejected; reason: the source transition function is partial and no sink is added
--   - encoding: reachable Rabin pairs indexed by canonical identifiers or colour classes, omitting empty accepting components → Finset of pairs built from actual reachable triples and nonempty merged accepting sets; reason: this uses the published condition convention; both unions still include all names in each class, and exact counts require distinct surviving pairs
--   - reading: Step 4 calls nodes whose descendants are deleted accepting, without explicitly resolving nested resets → the published annotations keep accepting marks only at topmost resetting nodes that survive compression; reason: a reset below one of these nodes is deleted; any old deleted node is unstable, as specified in Remark 8
--   - encoding: Ic has the finite canonical identifiers as its values → the subtype of the image of (weight, cf) on fullTree n; reason: all and only attained identifiers are colours, with the weight coordinate retained
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Theorem 24, p. 20

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, theorem 24. Statement only. -/
theorem theorem_24 {Q Sigma : Type} [Fintype Q] [Nonempty Q] [Fintype Sigma]
    (B : NBW Q Sigma) :
    transitionLanguage B (reducedCondition B) = language B := by sorry

end BuchiRabinIndex.LowerBound.Supplement
