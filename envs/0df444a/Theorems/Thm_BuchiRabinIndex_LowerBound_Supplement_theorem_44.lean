-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_44
-- name    : BuchiRabinIndex.LowerBound.Supplement.theorem_44
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T13:55:13.747087+00:00
-- url     : https://prove2.me/theorems/a639f40e-b0f3-4494-9ae4-c6d4b00e4375
-- title:
--   Theorem 44 — Correct mergings are proper colourings; both minimum indices equal χ
-- statement:
--   Let $n\ge1$, $I$ be any finite colour set, and $I_d:T^{(n)}\to I$ any map. If $I_d$ is coexistence-respecting, its merged condition recognizes $L(B)$ for every NBW $B$ with $n$ states and finite alphabet. If it is not coexistence-respecting, then
--   $$L(RT(F_n)^{I_d})\ne L(F_n).$$
--   Moreover, both the set of attainable merging indices correct for $F_n$ and the set of uniform attainable indices correct for every $n$-state input have the attained least element $\chi(G_n)$. For the uniform set, the index bounds every input and is attained on $F_n$. Finally,
--   $$\omega(G_n)\le\chi(G_n)\le\sum_{w=0}^{n-1}\operatorname{sf}(n,w).$$
--   Thus both correctness directions, both minimum characterizations with attainment, and both graph inequalities are asserted. The statement makes no claim that the chromatic and clique numbers agree.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
--   - encoding: labels are defined on the tree node set → the published History subtype extends labels by the empty set outside its node set; reason: the normalized extension is unique and introduces no history states
--   - encoding: the deterministic history trace may cease when the root is deleted or its initial label is empty → published Option successor and initial history; an absent infinite trace is rejected; reason: the source transition function is partial and no sink is added
--   - encoding: reachable Rabin pairs indexed by canonical identifiers or colour classes, omitting empty accepting components → Finset of pairs built from actual reachable triples and nonempty merged accepting sets; reason: this uses the published condition convention; both unions still include all names in each class, and exact counts require distinct surviving pairs
--   - reading: Step 4 calls nodes whose descendants are deleted accepting, without explicitly resolving nested resets → the published annotations keep accepting marks only at topmost resetting nodes that survive compression; reason: a reset below one of these nodes is deleted; any old deleted node is unstable, as specified in Remark 8
--   - encoding: n labelled states q1 through qn in F_n → the published Fin n states with qi represented by i-1; reason: the full automaton, initial state q1 and sole accepting state qn are unchanged
--   - encoding: minimum index correct for all n-state inputs, equivalently for F_n → IsLeast of uniformIndices and fullIndices, enumerating finite colour carriers as Fin k; reason: membership asserts attainment; the uniform bound is witnessed on F_n and also bounds every n-state input
--   - encoding: the finite chromatic numbers of G_n and its weight subgraphs → Mathlib chromaticNumber converted to Nat; reason: these graphs have finite carriers, so their chromatic numbers are finite; no infinite default is used
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Theorem 44, p. 29

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, theorem 44. Statement only. -/
theorem theorem_44 (n : ℕ) (hn : 1 ≤ n) :
    (∀ (I : Type) [Fintype I] (Id : Vertex n → I),
      (CoexistenceRespecting Id → UniversallyCorrect Id) ∧
      (¬ CoexistenceRespecting Id →
        transitionLanguage (fullBuchi n hn) (mergedCondition (fullBuchi n hn) Id) ≠
          language (fullBuchi n hn))) ∧
    IsLeast (uniformIndices n hn) (chi n) ∧
    IsLeast (fullIndices n hn) (chi n) ∧
    omega n ≤ chi n ∧ chi n ≤ ∑ w ∈ Finset.range n, sf n w := by sorry

end BuchiRabinIndex.LowerBound.Supplement
