-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_5_2
-- name    : ExactPatternStream.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:47.458371+00:00
-- url     : https://prove2.me/theorems/cd0c2f0e-454b-4628-9fb1-2472f48ce19f
-- title:
--   Lemma 5.2 — completeness: $\mathrm{Occ}(P,T)\subseteq M$
-- statement:
--   Let $M$ be the set returned by $\mathrm{Match}(P,T)$, Algorithm 2. Then
--   $$\mathrm{Occ}(P,T)\subseteq M,$$
--   for every choice of the hash functions $F_i$ and $f_R$. There are no false negatives, on any seeds, which makes the error of the algorithm one-sided.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $F_i$ of the form (6), "specified in Section 7.3" → an arbitrary argument `F`, with values $(y,z,\alpha)$; reason: §§4–5 of the source are written for any such $F_i$, and (14) is one
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
--   - encoding: $M$ a set of positions → $M$ a `Finset ℤ`; reason: $\gamma_h(e)-|P|$ is an integer subtraction, and it must not truncate
--   - generalization: $f_R$ of §7.4 → an arbitrary function `fR`; reason: the proof compares hashes of identical strings, so §7.4 is a special case
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 5.2, p.14 (PDF 15)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 5.2, p.14 (PDF 15).

Completeness: `Occ(P, T) ⊆ M` for the set `M` returned by `Match(P, T)`, Algorithm 2, for every choice of the hash functions `F_i` and `f_R`.

**Formalization Note.** The statement is deterministic: "even if the hash functions have collisions elsewhere" (p.13). `M` is a set of integers, so occurrences are cast to `ℤ`. -/
theorem lemma_5_2 {β : Type*} [DecidableEq β] (F : GroupHash) (fR : List Leaf → β) (P T : List ℕ)
    (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length) (hn : T.length ≤ 2 * P.length) :
    ∀ a ∈ occ P T, (a : ℤ) ∈ matchSet F fR P T := by sorry

end ExactPatternStream
