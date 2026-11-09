-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_5_7
-- name    : ChangingCache.UpperBound.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:55.224201+00:00
-- url     : https://prove2.me/theorems/fb3815e5-d22e-44df-884f-6ca8b0c42b32
-- title:
--   Lemma 5.7 — Keeping
-- statement:
--   Let $r'<r\le n$ be positions of a reduced run $(m,\sigma,\mathrm{OPT})$ under $(2,3)$ augmentation with
--   $$r\ \le\ 3F_{OPT}(r'+1)+2 .$$
--   Then there is a reduced run of length $r$ on the requests $\sigma_1,\dots,\sigma_r$, with a profile $m'$ satisfying $m'(j)=m(j)$ for $j\le F_{OPT}(r'+1)$ and an OPT, written with primes, in which
--   1. LRU has the same cache after every request;
--   2. OPT hits and misses at the same requests as before;
--   3. after every request $\sigma_u$ with $r'\le u\le r$, OPT holds the pages of $P_{OPT}(r')$ together with the pages it loaded in $(r',u]$.
--
--   In particular, for all $r'\le u\le r$,
--   $$B_3'(u)=B_3(u),\qquad P_{OPT}(u)\subseteq P'_{OPT}(u),\qquad |P'_{OPT}(u)|=|P_{OPT}(r')|+F_{OPT}(u)-F_{OPT}(r').$$
--
--   The lemma raises the profile beyond LRU's reach to a ramp so that OPT can keep every page it loads; it is applied twice in the earliest-failure argument.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
--   - encoding: LRU has the same cache after every request; OPT hits and misses at the same requests → for $u\le r$ LRU's ordered cache after $\sigma_1,\dots,\sigma_u$ is the same list on $m'$ as on $m$; for each request $i<r$ (0-based) the new OPT misses iff the old one does; reason: Lean convention; the cache as a list also fixes the recency order, which is determined by the requests
--   - encoding: OPT holds the pages of $P_{OPT}(r')$ together with the pages it loaded in $(r',u]$ → $P'_{OPT}(u)=P_{OPT}(r')\cup$ `loadedIn σ S r' u`; reason: the cardinality clause of the source shows that it holds exactly these pages
--   - encoding: $|P'_{OPT}(u)|=|P_{OPT}(r')|+F_{OPT}(u)-F_{OPT}(r')$ → $|P'_{OPT}(u)|+F_{OPT}(r')=|P_{OPT}(r')|+F_{OPT}(u)$ in $\mathbb N$; reason: the subtraction moved across; $F_{OPT}(r')\le F_{OPT}(u)$
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 5.7, p. 14

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

namespace ChangingCache.UpperBound

/-- **Lemma 5.7 (Keeping)**, p. 14. Let `r' < r` be positions of a reduced run `(m, σ, S)` under
`(2, 3)` augmentation with `r ≤ 3 F_OPT(r' + 1) + 2`. Then there is a reduced run of length `r` on
the requests `σ₁, …, σ_r`, with a profile `m'` satisfying `m'(j) = m(j)` for `j ≤ F_OPT(r' + 1)`
and an OPT `S'`, in which
* LRU has the same cache after every request,
* OPT hits and misses at the same requests as before, and
* after every request `σ_u` with `r' ≤ u ≤ r`, OPT holds the pages of `P_OPT(r')` together with the
  pages it loaded in `(r', u]`.
In particular, for all `r' ≤ u ≤ r`: `B₃'(u) = B₃(u)`, `P_OPT(u) ⊆ P'_OPT(u)` and
`|P'_OPT(u)| = |P_OPT(r')| + F_OPT(u) - F_OPT(r')`. -/
theorem lemma_5_7 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) (r' r : ℕ) (hrr : r' < r) (hr : r ≤ σ.length)
    (hcond : r ≤ 3 * policyMisses σ S (r' + 1) + 2) :
    ∃ (m' : ℕ → ℕ) (S' : ℕ → Finset α),
      IsReduced 2 3 m' (σ.take r) S' ∧
      (∀ j ≤ policyMisses σ S (r' + 1), m' j = m j) ∧
      (∀ u ≤ r, (lruRun (augCap 2 3 m') (σ.take u)).cache =
        (lruRun (augCap 2 3 m) (σ.take u)).cache) ∧
      (∀ i < r, missB (σ.take r) S' i = missB σ S i) ∧
      (∀ u, r' ≤ u → u ≤ r → S' u = S r' ∪ loadedIn σ S r' u) ∧
      (∀ u, r' ≤ u → u ≤ r →
        bank3 m' (σ.take r) S' u = bank3 m σ S u ∧
        S u ⊆ S' u ∧
        (S' u).card + policyMisses σ S r' = (S r').card + policyMisses σ S u) := by sorry

end ChangingCache.UpperBound
