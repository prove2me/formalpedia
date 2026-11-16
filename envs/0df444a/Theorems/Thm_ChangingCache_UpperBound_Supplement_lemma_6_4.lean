-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_Supplement_lemma_6_4
-- name    : ChangingCache.UpperBound.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:57.90243+00:00
-- url     : https://prove2.me/theorems/1168ba1d-1e57-4f65-b8a6-4e453fbfa594
-- title:
--   Lemma 6.4 — Second drop and perpetual separation
-- statement:
--   Continue the Section 6.2 first-drop construction, with the same staircase, height interval and plateau as in Lemma 6.3. Let $r_f=r_N+b_N+h+1$. Suppose
--   $$B_2(r_f)\le-3,\qquad |U(r_f)|\ge3,\qquad U(r_f)\subseteq P_{\mathrm{LRU}}(r_f).$$
--   Set $p=\lfloor r_f/2\rfloor+1$ and replace the profile from entry $p$ onward by height one. The generated requests and useful pages through $r_f$ are unchanged. There exists $d\in\{1,2\}$ such that the next $d$ requests are new, and after them
--   $$C_{\mathrm{LRU}}=2,\qquad F_S(r_f+d)<p.$$
--   Every later request hits in the same policy and misses in LRU. Every finite prefix of the completed construction is legal, all policy misses are cold, and all requests miss in LRU.
--
--   This turns the first drop into a permanent separation on one consistent stream, rather than separate finite witnesses. The original first-drop context is essential: $r_f$ is its constructed endpoint, not an arbitrary cache state satisfying only three numerical tests.
--
--   Differences from the source:
--   - encoding: the Section 6 greedy adversary and its useful-page policy → the recursive greedyRun and greedyPolicy with an arbitrary valid finite-set picker and request-position names for fresh pages; reason: this implements every greedy tie choice; renaming fresh pages changes no cache event
--   - encoding: useful pages immediately after a request, with discards at the next miss → greedyRun.useful before advance discards, and greedyPolicy after discards before the next request; temporary non-useful incoming pages are discarded immediately; reason: the temporary page is in LRU and is never selected again; earlier voluntary discards preserve all hits, misses and capacity checks in the published snapshot convention
--   - encoding: integer heights, signed banks, one-based request names and profile entries starting at zero → signed integer stage arithmetic followed by natural indices, lists indexed from zero and a real-valued bank; reason: positive source lengths and request positions make the conversions exact; no negative bank is truncated
--   - encoding: the constructed legal OPT policy has only cold misses and every request misses in LRU → IsLegal, AllMissesCold and LRUAlwaysMisses are explicit conclusions about the constructed histories; reason: OPT and the Section 6 run conventions are certified rather than assumed as invariant hypotheses
--   - encoding: r_f is the endpoint of the first-drop construction in Section 6.2 → the staircase, first-drop height interval and plateau are explicit binders; r_f is computed from N and h; reason: these are inherited construction assumptions, not additional assumptions on Theorem 1.2; they retain the useful pages recency order and the unread plateau without assuming a proved invariant
--   - encoding: at most two new requests before perpetual OPT hits and LRU misses → a number d with 1 ≤ d ≤ 2, fresh request-position names for those requests, and quantified hit/miss assertions for every later position; reason: the next profile entry needs one or two LRU misses; naming and quantifying the events preserves the full timing claim
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), p. 20, Lemma 6.4; inherited Section 6.2 setup pp. 19–20

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Supplement_Adversary

namespace ChangingCache.UpperBound.Supplement

/-- Lemma 6.4, p. 20, in its Section 6.2 context: r_f is the end of the first drop,
not an arbitrary cache state. The first-drop plateau extends up to the new drop. -/
theorem lemma_6_4 (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (N : ℕ) (h : ℤ)
    (hm : IsMemoryProfile m) (hpick : IsPicker pick) (hstairs : StaircaseThrough m N)
    (hlo : 2 * stageB N + 4 ≤ h) (hhi : 2 * h ≤ stageK (N + 1) + stageB N)
    (hplateau : ∀ j : ℕ, stageT N < (j : ℤ) →
      (j : ℤ) ≤ stageT N + halfCeil h → (m j : ℤ) = h) :
    let rf := (stageRequest N + stageB N + h + 1).toNat
    bank 2 m (greedyRun m pick rf).history (greedyPolicy m pick) rf ≤ -3 →
    3 ≤ (greedyRun m pick rf).useful.length →
    (greedyRun m pick rf).useful.toFinset ⊆
      (lruRun (augCap 2 2 m) (greedyRun m pick rf).history).cache.toFinset →
    let p := rf / 2 + 1
    let m' := finalDrop m p
    (greedyRun m' pick rf).history = (greedyRun m pick rf).history ∧
    (greedyRun m' pick rf).useful = (greedyRun m pick rf).useful ∧
    (∀ n, IsLegal m' (greedyRun m' pick n).history (greedyPolicy m' pick) ∧
      AllMissesCold (greedyRun m' pick n).history (greedyPolicy m' pick) ∧
      LRUAlwaysMisses (augCap 2 2 m') (greedyRun m' pick n).history) ∧
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ∧
      (∀ j < d, greedyStream m' pick (rf + j) = rf + j + 1) ∧
      augCap 2 2 m' (lruRun (augCap 2 2 m') (greedyRun m' pick (rf + d)).history).misses = 2 ∧
      (greedyRun m' pick (rf + d)).misses < p ∧
      ∀ j, rf + d ≤ j →
        greedyStream m' pick j ∈ greedyPolicy m' pick j ∧
        greedyStream m' pick j ∉
          (lruRun (augCap 2 2 m') (greedyRun m' pick j).history).cache := by sorry

end ChangingCache.UpperBound.Supplement
