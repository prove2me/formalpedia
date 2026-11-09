-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_5_6
-- name    : ChangingCache.UpperBound.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:15.617596+00:00
-- url     : https://prove2.me/theorems/bf86f83f-ad90-493f-a6c6-8937339e4cae
-- title:
--   Lemma 5.6 — Counting
-- statement:
--   Let $i$ be a position of a reduced run under $(2,3)$ augmentation, and let $u\le i-|P_{LRU}(i)|$. Then
--   $$|P_{OPT}(u)|+F_{OPT}(i)-F_{OPT}(u)\ \ge\ |P_{LRU}(i)|+\mu(i).$$
--   That is, the pages OPT held at $u$ and the pages it loaded in $(u,i]$ together cover LRU's window at $i$ and the $\mu(i)$ pages of OPT outside it.
--
--   The final proof of Theorem 5.1 applies the lemma at the earliest failure $y$ of Eq. (4), with $u=b$ and $u=a$.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
--   - encoding: $u\le i-|P_{LRU}(i)|$ and $|P_{OPT}(u)|+F_{OPT}(i)-F_{OPT}(u)\ge|P_{LRU}(i)|+\mu(i)$ → $u+|P_{LRU}(i)|\le i$ and $|P_{LRU}(i)|+\mu(i)+F_{OPT}(u)\le|P_{OPT}(u)|+F_{OPT}(i)$ in $\mathbb N$; reason: the subtractions moved across; equivalent since $F_{OPT}(u)\le F_{OPT}(i)$ for $u\le i$
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 5.6, p. 13

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

namespace ChangingCache.UpperBound

/-- **Lemma 5.6 (Counting)**, p. 13. Let `i` be a position of a reduced run under `(2, 3)`
augmentation and `u ≤ i - |P_LRU(i)|`. Then
`|P_OPT(u)| + F_OPT(i) - F_OPT(u) ≥ |P_LRU(i)| + μ(i)`
(stated with the subtraction moved across, all in `ℕ`). -/
theorem lemma_5_6 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    ∀ i ≤ σ.length, ∀ u, u + (lruCache (augCap 2 3 m) σ i).card ≤ i →
      (lruCache (augCap 2 3 m) σ i).card + mu m σ S i + policyMisses σ S u ≤
        (S u).card + policyMisses σ S i := by sorry

end ChangingCache.UpperBound
