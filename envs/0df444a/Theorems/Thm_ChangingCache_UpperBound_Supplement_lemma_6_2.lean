-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_Supplement_lemma_6_2
-- name    : ChangingCache.UpperBound.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:26:30.012284+00:00
-- url     : https://prove2.me/theorems/9019d99c-d382-401c-8a13-e6305a66f78f
-- title:
--   Lemma 6.2 — Full staircase stage invariant
-- statement:
--   Let $m$ be any legal memory profile following the Section 6 staircase through stage $N$, and run the greedy adversary with any valid tie rule. Write $U(r)$ for its useful pages, $F_S(r)$ for its policy miss count and $\lambda(r)=\lfloor r/2\rfloor$. For every $0\le i\le N$, after $r_i=2T_i-b_i$ requests,
--   $$F_S(r_i)=T_i,\qquad B_2(r_i)=b_i,\qquad |U(r_i)|=K_{i+1}-1.$$
--   The useful pages, in recency order, are exactly the first $K_{i+1}-1$ pages of LRU's recency stack. Moreover,
--   $$\lambda(r_i)=T_i-\lceil b_i/2\rceil;\qquad
--    i\ge1\ \Longrightarrow\ \lambda(r_i)=F_i\ \hbox{and LRU is full}.$$
--   The constructed policy is legal and has only cold misses, and every request misses in LRU. In particular the policy is prefix optimal by the published Observation 3.1. No fullness claim is made at stage zero.
--
--   This is the complete stage invariant supporting Theorem 1.2, including the cold-rise initialization and all three clauses (I1)–(I3).
--
--   Differences from the source:
--   - encoding: the Section 6 greedy adversary and its useful-page policy → the recursive greedyRun and greedyPolicy with an arbitrary valid finite-set picker and request-position names for fresh pages; reason: this implements every greedy tie choice; renaming fresh pages changes no cache event
--   - encoding: useful pages immediately after a request, with discards at the next miss → greedyRun.useful before advance discards, and greedyPolicy after discards before the next request; temporary non-useful incoming pages are discarded immediately; reason: the temporary page is in LRU and is never selected again; earlier voluntary discards preserve all hits, misses and capacity checks in the published snapshot convention
--   - encoding: integer heights, signed banks, one-based request names and profile entries starting at zero → signed integer stage arithmetic followed by natural indices, lists indexed from zero and a real-valued bank; reason: positive source lengths and request positions make the conversions exact; no negative bank is truncated
--   - encoding: the constructed legal OPT policy has only cold misses and every request misses in LRU → IsLegal, AllMissesCold and LRUAlwaysMisses are explicit conclusions about the constructed histories; reason: OPT and the Section 6 run conventions are certified rather than assumed as invariant hypotheses
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), pp. 17–18, Lemma 6.2 (proof continues p. 19)

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Supplement_Adversary

namespace ChangingCache.UpperBound.Supplement

/-- Lemma 6.2, pp. 17–18: all three stage clauses, including stage zero.
The legal/cold/all-miss clauses expose the meaning of the operational OPT/LRU run. -/
theorem lemma_6_2 (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (N : ℕ)
    (hm : IsMemoryProfile m) (hpick : IsPicker pick) (hstairs : StaircaseThrough m N) :
    ∀ i ≤ N,
      let r := (stageRequest i).toNat
      let st := greedyRun m pick r
      let σ := st.history
      let S := greedyPolicy m pick
      IsLegal m σ S ∧ AllMissesCold σ S ∧ LRUAlwaysMisses (augCap 2 2 m) σ ∧
      policyMisses σ S r = (stageT i).toNat ∧
      bank 2 m σ S r = (stageB i : ℝ) ∧
      (st.useful.length : ℤ) = stageK (i + 1) - 1 ∧
      st.useful = (lruRun (augCap 2 2 m) σ).stack.take (stageK (i + 1) - 1).toNat ∧
      ((r / 2 : ℕ) : ℤ) = stageT i - halfCeil (stageB i) ∧
      (1 ≤ i → ((r / 2 : ℕ) : ℤ) = stageF i ∧
        (lruRun (augCap 2 2 m) σ).cache.length = augCap 2 2 m r) := by sorry

end ChangingCache.UpperBound.Supplement
