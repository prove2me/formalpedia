-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_observation_3_1
-- name    : ChangingCache.UpperBound.observation_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:56.491581+00:00
-- url     : https://prove2.me/theorems/48bc2959-bad5-4482-83dd-4df630514443
-- title:
--   Observation 3.1 — a legal policy with only cold misses is optimal on every prefix
-- statement:
--   Let $m$ be a sequence of capacities and $\sigma$ a request sequence of length $n$, and let $P$ be a legal policy on $m$ all of whose misses are cold. Then for every $0\le r\le n$, the number of misses of $P$ among the first $r$ requests equals OPT's number of misses on the prefix $(\sigma_1,\dots,\sigma_r)$:
--   $$F_P(r)=F_{OPT}(\sigma_1,\dots,\sigma_r).$$
--
--   Every policy starts empty and loads a page only when it is requested, so every policy misses at least on cold requests; this observation turns "only cold misses" into optimality, and it is used by Lemma 4.3, Lemma 4.7 and Lemma 5.7 to certify that a transformed policy is still OPT.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: OPT, the legal policy with the fewest misses → `optMisses m σ`, the infimum over legal policies of their miss count (attained, the set being nonempty for a memory profile); reason: Lean convention; the minimum of a nonempty set of natural numbers
--   - encoding: optimal after every prefix of the request sequence → the policy's miss count after the first $r$ requests equals `optMisses m (σ.take r)` for every $r\le n$; reason: a policy is optimal on a prefix when its miss count there is the minimum over legal policies on that prefix, and the restriction of a legal policy to a prefix is legal
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Observation 3.1, p. 6

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Model

namespace ChangingCache.UpperBound

/-- **Observation 3.1** (p. 6): a legal policy that has only cold misses is optimal after every
prefix of the request sequence: after the first `r` requests its miss count equals OPT's on that
prefix. -/
theorem observation_3_1 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α)
    (S : ℕ → Finset α) (hS : IsLegal m σ S) (hcold : AllMissesCold σ S) :
    ∀ r ≤ σ.length, policyMisses σ S r = optMisses m (σ.take r) := by sorry

end ChangingCache.UpperBound
