-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_29
-- name    : BuchiRabinIndex.LowerBound.Supplement.theorem_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T13:54:19.113166+00:00
-- url     : https://prove2.me/theorems/9f268ca4-870c-4fa5-b747-ab18d5114a50
-- title:
--   Theorem 29 — Full Büchi automata attain the exact reduced pair count
-- statement:
--   For every $n\ge1$, take the published full Büchi automaton $F_n$, whose initial state is $q_1$ and whose sole accepting state is $q_n$. The reachable reduced condition has exactly
--   $$|\lambda_{RT'(F_n)}|=\begin{cases}3\cdot2^{n/2-1}-1&n\text{ even},\\2^{(n+1)/2}-1&n\text{ odd}.\end{cases}$$
--   This is equality of the number of distinct reachable accepting pairs after empty accepting components have been omitted. It requires reachable accepting witnesses for every canonical identifier, not merely a count of possible identifiers. For $n=1$ the count is 1.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
--   - encoding: labels are defined on the tree node set → the published History subtype extends labels by the empty set outside its node set; reason: the normalized extension is unique and introduces no history states
--   - encoding: the deterministic history trace may cease when the root is deleted or its initial label is empty → published Option successor and initial history; an absent infinite trace is rejected; reason: the source transition function is partial and no sink is added
--   - encoding: reachable Rabin pairs indexed by canonical identifiers or colour classes, omitting empty accepting components → Finset of pairs built from actual reachable triples and nonempty merged accepting sets; reason: this uses the published condition convention; both unions still include all names in each class, and exact counts require distinct surviving pairs
--   - reading: Step 4 calls nodes whose descendants are deleted accepting, without explicitly resolving nested resets → the published annotations keep accepting marks only at topmost resetting nodes that survive compression; reason: a reset below one of these nodes is deleted; any old deleted node is unstable, as specified in Remark 8
--   - encoding: Ic has the finite canonical identifiers as its values → the subtype of the image of (weight, cf) on fullTree n; reason: all and only attained identifiers are colours, with the weight coordinate retained
--   - encoding: n labelled states q1 through qn in F_n → the published Fin n states with qi represented by i-1; reason: the full automaton, initial state q1 and sole accepting state qn are unchanged
--   - encoding: the threshold is ceil((n-1)/2) for positive n → natural division n / 2; reason: these integers agree for every n ≥ 1; all subtractions and exponents are exact on the stated branches
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Theorem 29, p. 22

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, theorem 29. Statement only. -/
theorem theorem_29 (n : ℕ) (hn : 1 ≤ n) :
    (Even n → (reducedCondition (fullBuchi n hn)).card = 3 * 2 ^ (n / 2 - 1) - 1) ∧
    (Odd n → (reducedCondition (fullBuchi n hn)).card = 2 ^ ((n + 1) / 2) - 1) := by sorry

end BuchiRabinIndex.LowerBound.Supplement
