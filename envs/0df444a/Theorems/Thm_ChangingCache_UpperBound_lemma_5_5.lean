-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_lemma_5_5
-- name    : ChangingCache.UpperBound.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:57.381196+00:00
-- url     : https://prove2.me/theorems/ddb04eb7-95cc-4183-9eb7-f22fcaffb3cd
-- title:
--   Lemma 5.5 — slack at least $-1$ before the first failure of Eq. (4)
-- statement:
--   Consider a reduced run of length $n$ under $(2,3)$ augmentation with slack $S_3(i)=B_3(i)-|P_{OPT}(i)|$. Let $w$ be the least position $1\le w\le n$ with $w\equiv1\pmod3$ at which Equation (4), $B_3(w)\ge|P_{OPT}(w)|+\mu(w)$, fails, or $w=n+1$ if it never fails. Then for every $w'<w$,
--   $$S_3(w')\ge-1,\qquad\text{that is}\qquad |P_{OPT}(w')|\le B_3(w')+1 .$$
--
--   The lemma transfers the invariant, which holds only at positions $\equiv1\pmod3$, to every earlier position at the price of one unit of slack; it is applied at the positions $a$ and $b$ of the earliest-failure argument.
--
--   Differences from the source:
--   - encoding: a page is an identifier; a request sequence is a finite list $\sigma_1,\dots,\sigma_n$ → pages are elements of an arbitrary type with decidable equality; the sequence is a `List`, request $\sigma_{i+1}$ is the 0-based entry `σ[i]` and position $i$ is the moment after the first $i$ requests; reason: Lean convention; same instances
--   - encoding: a legal policy may discard pages at any time; on its $j$-th miss the loaded page must fit capacity $m(j)$ → a policy is the family $S_i$ of pages held after the first $i$ requests, including the discards made before request $i+1$: $S_0=\emptyset$, $S_{i+1}\subseteq S_i\cup\{\sigma_{i+1}\}$, and $|S_i|+1\le m(j)$ at its $j$-th miss; reason: moving a discard earlier, to just after the previous request, changes no hit, miss or capacity check; this is the placement the source itself uses in (R3) and Eq. (5)
--   - encoding: $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)) → `augCap 2 3 m k` $=2\,m(\lfloor k/3\rfloor_+)$ with the real speed $3$; reason: the same capacity law as Section 4 at $(a,s)=(2,3)$; it equals $2m(k\,\mathrm{div}\,3)$
--   - encoding: a reduced run of OPT and LRU on a memory profile $m$ → `IsReduced 2 3 m σ S`: $m$ is a memory profile, $S$ is an optimal legal policy for $\sigma$ on $m$, and (R1)–(R3) hold; reason: Definition 4.1 transcribed; OPT is a designated optimal policy of the run
--   - reading: "let $w$ be the least position at which Equation (9) fails" → Equation (4), at positions $1\le w\le n$ with $w\equiv1\pmod3$ (`eq4FirstFailure`); reason: the paragraph before the lemma and its proof use Equation (4) ("By the choice of $w$, Equation (4) holds at $w_1'$"); the actual Eq. (9) on p. 16, $2s\le d-\mu$, is stated with the variables $x,a,d,s$ of a globally earliest failure, which a generic reduced run does not have: for $m\equiv1$ and the one-request sequence $(p)$ (a reduced run, Eq. (4) holding at position 1 since $B_3(1)=2\ge|P_{OPT}(1)|+\mu(1)=1$) no failing position exists and Eq. (9) is undefined
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Lemma 5.5, p. 13 (the printed reference "Equation (9)" read as Equation (4))

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

namespace ChangingCache.UpperBound

/-- **Lemma 5.5**, p. 13 (the printed cross-reference "Equation (9)" read as Equation (4)). In a
reduced run of length `n` under `(2, 3)` augmentation, let `w` be the least position
`1 ≤ w ≤ n`, `w ≡ 1 (mod 3)`, at which Equation (4) fails, or `w = n + 1` if it never fails. Then
`S₃(w') ≥ -1`, that is `|P_OPT(w')| ≤ B₃(w') + 1`, for every `w' < w`. -/
theorem lemma_5_5 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    ∀ w' < eq4FirstFailure m σ S, -1 ≤ slack3 m σ S w' := by sorry

end ChangingCache.UpperBound
