-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_5_4
-- name    : ChangingCache.UpperBound.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:11.338205+00:00
-- url     : https://prove2.me/theorems/22d1986b-7b59-4f12-9f67-5e9c3deda3c0
-- title:
--   Lemma 5.4 — the first negative bank violates Eq. (4)
-- statement:
--   Consider a reduced run of length $n$ under $(2,3)$ augmentation with bank $B_3(i)=3F_{OPT}(i)-F_{LRU}(i)$. If some step $r\le n$ has $B_3(r)<0$, let $i$ be the least index with $B_3(i)<0$. Then
--   1. $i\equiv1\pmod3$;
--   2. $B_3(u)\ge0$ for all $u<i$;
--   3. Equation (4) fails at $i$: $B_3(i)<|P_{OPT}(i)|+\mu(i)$.
--
--   So Theorem 5.1 follows once Equation (4) is shown to hold at every position.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
--   - encoding: the least index $i$ with $B_3(i)<0$ → `sInf {r | r ≤ n ∧ B₃ r < 0}`, under the hypothesis that this set is nonempty; reason: indices are the positions $0,\dots,n$ of the run
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 5.4, p. 13

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

namespace ChangingCache.UpperBound

/-- **Lemma 5.4**, p. 13. If a reduced run under `(2, 3)` augmentation has some step `r` with
`B₃(r) < 0`, let `i` be the least index with `B₃(i) < 0`. Then `i ≡ 1 (mod 3)`, `B₃(u) ≥ 0` for all
`u < i`, and Equation (4) fails at `i`. -/
theorem lemma_5_4 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) (hneg : ∃ r ≤ σ.length, bank3 m σ S r < 0) :
    sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0} % 3 = 1 ∧
      (∀ u < sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0}, 0 ≤ bank3 m σ S u) ∧
      ¬ Eq4At m σ S (sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0}) := by sorry

end ChangingCache.UpperBound
