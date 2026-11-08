-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_4_16
-- name    : ExactPatternStream.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:48.395196+00:00
-- url     : https://prove2.me/theorems/603c979d-6775-4e2b-84a5-bc23ad935b3f
-- title:
--   Lemma 4.16 — $\sum_{i<h}\log(c_i+2)=O(\log m)$
-- statement:
--   For every choice of the hash functions,
--   $$\sum_{0\le i<h}\log(c_i+2)=O(\log m).$$
--   Wide levels are paid for by there being few of them; this is the telescoping behind the $O(\log n\log\log n)$ total.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $F_i$ of the form (6), "specified in Section 7.3" → an arbitrary argument `F`, with values $(y,z,\alpha)$; reason: §§4–5 of the source are written for any such $F_i$, and (14) is one
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.16, p.13 (PDF 14)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.16, p.13 (PDF 14).

`Σ_{0≤i<h} log(c_i + 2) = O(log m)`, for every choice of the hash functions.

**Formalization Note.** `O(log m)` is one absolute `K` before all variables, with `log₂` throughout. At `m = 1` the sum is empty. -/
theorem lemma_4_16 : ∃ K : ℝ, ∀ (F : GroupHash) (P T : List ℕ), 1 ≤ P.length → P.length ≤ T.length →
    T.length ≤ 2 * P.length →
    let B := build F P T
    ∑ i ∈ Finset.range (topIndex B), Real.logb 2 (((lvl B i).c : ℝ) + 2) ≤
      K * Real.logb 2 P.length := by sorry

end ExactPatternStream
