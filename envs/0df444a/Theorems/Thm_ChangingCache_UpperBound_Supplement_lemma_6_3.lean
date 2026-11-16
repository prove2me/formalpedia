-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_Supplement_lemma_6_3
-- name    : ChangingCache.UpperBound.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:18.580961+00:00
-- url     : https://prove2.me/theorems/8b8fbf03-7fbf-4840-abdb-a7299328f062
-- title:
--   Lemma 6.3 — First drop and exact negative bank
-- statement:
--   Let $m$ follow the Section 6 staircase through stage $N$, and let the integer drop height $h$ satisfy
--   $$2b_N+4\le h\le (K_{N+1}+b_N)/2.$$
--   Assume the profile has height $h$ at entries $T_N+1,\ldots,T_N+\lceil h/2\rceil$. For any greedy tie rule, the first-drop construction retains the $h-1$ least recently requested old useful pages. At request
--   $$r_f=r_N+b_N+h+1$$
--   it has
--   $$B_2(r_f)=2b_N+3-h<0,\qquad |U(r_f)|=h-1,\qquad U(r_f)\subseteq P_{\mathrm{LRU}}(r_f).$$
--   The constructed policy is legal, all its misses are cold, and all requests miss in LRU. Entries beyond the stated plateau are unrestricted, subject to being a legal memory profile.
--
--   This first-drop lemma supplies the exact negative bank and useful-page configuration needed by the second drop.
--
--   Differences from the source:
--   - encoding: the Section 6 greedy adversary and its useful-page policy → the recursive greedyRun and greedyPolicy with an arbitrary valid finite-set picker and request-position names for fresh pages; reason: this implements every greedy tie choice; renaming fresh pages changes no cache event
--   - encoding: useful pages immediately after a request, with discards at the next miss → greedyRun.useful before advance discards, and greedyPolicy after discards before the next request; temporary non-useful incoming pages are discarded immediately; reason: the temporary page is in LRU and is never selected again; earlier voluntary discards preserve all hits, misses and capacity checks in the published snapshot convention
--   - encoding: integer heights, signed banks, one-based request names and profile entries starting at zero → signed integer stage arithmetic followed by natural indices, lists indexed from zero and a real-valued bank; reason: positive source lengths and request positions make the conversions exact; no negative bank is truncated
--   - encoding: the constructed legal OPT policy has only cold misses and every request misses in LRU → IsLegal, AllMissesCold and LRUAlwaysMisses are explicit conclusions about the constructed histories; reason: OPT and the Section 6 run conventions are certified rather than assumed as invariant hypotheses
--   - encoding: h ≤ (K_{N+1}+b_N)/2 with integer h → 2*h ≤ K_{N+1}+b_N in integer arithmetic; reason: cross multiplication by positive two preserves the entire interval, including both endpoints
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), p. 19, Lemma 6.3; proof pp. 19–20

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Supplement_Adversary

namespace ChangingCache.UpperBound.Supplement

/-- Lemma 6.3, pp. 19–20. Later unread entries of the profile remain unrestricted. -/
theorem lemma_6_3 (m : ℕ → ℕ) (pick : Finset ℕ → ℕ) (N : ℕ) (h : ℤ)
    (hm : IsMemoryProfile m) (hpick : IsPicker pick) (hstairs : StaircaseThrough m N)
    (hlo : 2 * stageB N + 4 ≤ h) (hhi : 2 * h ≤ stageK (N + 1) + stageB N)
    (hplateau : ∀ j : ℕ, stageT N < (j : ℤ) →
      (j : ℤ) ≤ stageT N + halfCeil h → (m j : ℤ) = h) :
    let rf := (stageRequest N + stageB N + h + 1).toNat
    let st := greedyRun m pick rf
    let σ := st.history
    let S := greedyPolicy m pick
    IsLegal m σ S ∧ AllMissesCold σ S ∧ LRUAlwaysMisses (augCap 2 2 m) σ ∧
    bank 2 m σ S rf = ((2 * stageB N + 3 - h : ℤ) : ℝ) ∧
    bank 2 m σ S rf < 0 ∧
    (st.useful.length : ℤ) = h - 1 ∧
    st.useful.toFinset ⊆ (lruRun (augCap 2 2 m) σ).cache.toFinset := by sorry

end ChangingCache.UpperBound.Supplement
