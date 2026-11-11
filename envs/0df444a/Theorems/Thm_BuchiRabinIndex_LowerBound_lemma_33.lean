-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_33
-- name    : BuchiRabinIndex.LowerBound.lemma_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:29.874625+00:00
-- url     : https://prove2.me/theorems/43a274df-31fd-4f5f-bba8-27b4f71f40f5
-- title:
--   Lemma 33 — pinching
-- statement:
--   Fix $n\ge1$. Let $D_1,D_2,D$ be cycles in $RT(F_n)$, and suppose one Rabin pair $p=(A,R)$ accepts both $D_1$ and $D_2$. If
--   $$D_2\subseteq D\subseteq D_1\cup D_2,$$
--   then $p$ accepts $D$ as well: $D\cap A\ne\varnothing$ and $D\cap R=\varnothing$.
--
--   The containment is one-sided: the intermediate cycle must contain $D_2$. All cycles and the pair are arbitrary, and no canonical-node or merged-pair restriction is imposed.
--
--   Differences from the source:
--   - encoding: states q_1,...,q_n and alphabet 2^(Q×Q) → Fin n with q_i represented by i−1 and Finset transition relations; reason: this is a bijective indexing of all states and letters
--   - encoding: labels are functions defined on the node set → labels extend by the empty set outside the node set, with a validity subtype; reason: the extension is unique and adds no histories or transitions
--   - encoding: deterministic transitions may fail to have a successor → Option history trees, with a dying trace rejected by every condition; reason: root deletion has no history-tree successor; no sink is added
--   - encoding: sets of actual history-tree transitions → sets in the ambient carrier of history/letter/history triples, with actual successors enforced in traces and cycles; reason: nonactual triples never occur in a trace or cycle; source transition sets embed unchanged
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 33, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 33; statement only. -/
theorem lemma_33 (n : ℕ) (hn : 1 ≤ n)
    (p : RabinPair (Edge (Fin n) (Letter n)))
    (D1 D2 D : Set (Edge (Fin n) (Letter n)))
    (h1 : Cycle (fullBuchi n hn) D1) (h2 : Cycle (fullBuchi n hn) D2)
    (hD : Cycle (fullBuchi n hn) D) (hp1 : PairAccepts p D1) (hp2 : PairAccepts p D2)
    (hsub : D2 ⊆ D) (hsup : D ⊆ D1 ∪ D2) : PairAccepts p D := by sorry

end BuchiRabinIndex.LowerBound
