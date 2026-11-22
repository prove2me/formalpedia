-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_25
-- name    : BuchiRabinIndex.LowerBound.Supplement.theorem_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T13:53:35.20199+00:00
-- url     : https://prove2.me/theorems/2153c158-5dbb-4a89-ba42-b3ef6b3c0eae
-- title:
--   Theorem 25 — Reduced determinization: little-o states, exact index bounds, language
-- statement:
--   Let hist$(n)$ count all history states on $n$ labelled states. Uniformly in the input automaton,
--   $$\forall\varepsilon>0\ \exists N\ \forall n\ge N:\quad \operatorname{hist}(n)\le\varepsilon((165/100)n)^n.$$
--   For every NBW $B$ on any finite nonempty state carrier $Q$ and finite alphabet, put $n=|Q|$. Its history carrier is finite, has exactly hist$(n)$ states, and the reduced condition satisfies
--   $$|\lambda_{RT'}|\le\begin{cases}3\cdot2^{n/2-1}-1&n\text{ even},\\2^{(n+1)/2}-1&n\text{ odd},\end{cases}\qquad L(RT')=L(B).$$
--   The three source conclusions are retained together. No state-count estimate is a hypothesis; Schewe's estimate remains a proof dependency. The asymptotic threshold is independent of $B$, its alphabet and all other automaton data. The case $n=1$ is included.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
--   - encoding: labels are defined on the tree node set → the published History subtype extends labels by the empty set outside its node set; reason: the normalized extension is unique and introduces no history states
--   - encoding: the deterministic history trace may cease when the root is deleted or its initial label is empty → published Option successor and initial history; an absent infinite trace is rejected; reason: the source transition function is partial and no sink is added
--   - encoding: reachable Rabin pairs indexed by canonical identifiers or colour classes, omitting empty accepting components → Finset of pairs built from actual reachable triples and nonempty merged accepting sets; reason: this uses the published condition convention; both unions still include all names in each class, and exact counts require distinct surviving pairs
--   - reading: Step 4 calls nodes whose descendants are deleted accepting, without explicitly resolving nested resets → the published annotations keep accepting marks only at topmost resetting nodes that survive compression; reason: a reset below one of these nodes is deleted; any old deleted node is unstable, as specified in Remark 8
--   - encoding: Ic has the finite canonical identifiers as its values → the subtype of the image of (weight, cf) on fullTree n; reason: all and only attained identifiers are colours, with the weight coordinate retained
--   - encoding: the finite history-state count hist(n) and o((1.65n)^n) → Nat.card with finiteness and relabelling equality in the conclusion, and a uniform epsilon/threshold inequality with exact real 165/100; reason: the conclusion rules out the infinite-cardinality default and states the same little-o estimate for all sufficiently large n
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Theorem 25, p. 21

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging
import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Counting

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, theorem 25. Statement only. -/
theorem theorem_25 :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (hist n : ℝ) ≤ ε * stateScale n) ∧
    (∀ (Q Sigma : Type) [Fintype Q] [Nonempty Q] [Fintype Sigma] (B : NBW Q Sigma),
      Finite (History Q) ∧ historyCount Q = hist (Fintype.card Q) ∧
      (Even (Fintype.card Q) →
        (reducedCondition B).card ≤ 3 * 2 ^ (Fintype.card Q / 2 - 1) - 1) ∧
      (Odd (Fintype.card Q) →
        (reducedCondition B).card ≤ 2 ^ ((Fintype.card Q + 1) / 2) - 1) ∧
      transitionLanguage B (reducedCondition B) = language B) := by sorry

end BuchiRabinIndex.LowerBound.Supplement
