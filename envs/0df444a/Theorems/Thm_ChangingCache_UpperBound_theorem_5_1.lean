-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_theorem_5_1
-- name    : ChangingCache.UpperBound.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:50.771089+00:00
-- url     : https://prove2.me/theorems/6f45d03a-9785-43c4-ab1e-0df03cc86fe5
-- title:
--   Theorem 5.1 — the $(2,3)$ upper bound for reduced runs
-- statement:
--   Under $(2,3)$ augmentation, every reduced run of length $n$ has
--   $$F_{LRU}(n)=n\ \le\ 3F_{OPT}(n).$$
--
--   Together with Corollary 4.2 (at $(a,s)=(2,3)$) this gives Theorem 1.1: a counterexample to the upper bound would yield a reduced run with $n>3F_{OPT}(n)$.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Theorem 5.1, p. 12 (proof pp. 14–16)

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-- **Theorem 5.1**, p. 12. Under `(2, 3)` augmentation, every reduced run of length `n` has
`F_LRU(n) = n ≤ 3 F_OPT(n)`. -/
theorem theorem_5_1 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    lruMissCount (augCap 2 3 m) σ σ.length = σ.length ∧
      σ.length ≤ 3 * policyMisses σ S σ.length := by sorry

end ChangingCache.UpperBound
