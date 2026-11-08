-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_4_15
-- name    : ExactPatternStream.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:39.494085+00:00
-- url     : https://prove2.me/theorems/85dc5645-b550-49eb-8800-a68afe233b92
-- title:
--   Lemma 4.15 — $h=O(\log m)$, $|\overline P_i|\le2^{i+1}m$, $|\overline T_i|\le2^in$
-- statement:
--   For every choice of the hash functions, the number of levels satisfies $h=O(\log m)$, and for every $0\le i\le h$,
--   $$|\overline P_i|\le2^{i+1}m,\qquad|\overline T_i|\le2^in.$$
--   These bounds underlie the space analysis, Lemma 4.16, and the degree count of Lemma 7.7.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $F_i$ of the form (6), "specified in Section 7.3" → an arbitrary argument `F`, with values $(y,z,\alpha)$; reason: §§4–5 of the source are written for any such $F_i$, and (14) is one
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.15, p.12 (PDF 13)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.15, p.12 (PDF 13).

`h = O(log m)`, and the unrolled strings grow by at most a factor `2` per level, for every choice of the hash functions.

**Formalization Note.** `O(log m)` is one absolute `K` before all variables, with `log₂`. At `m = 1`, `log₂ m = 0` and indeed `h = 0`, as `$ ◦ P` is a single run after the guard. -/
theorem lemma_4_15 : ∃ K : ℝ, ∀ (F : GroupHash) (P T : List ℕ), 1 ≤ P.length → P.length ≤ T.length →
    T.length ≤ 2 * P.length →
    let B := build F P T
    (topIndex B : ℝ) ≤ K * Real.logb 2 P.length ∧
      ∀ i ≤ topIndex B,
        (lvl B i).Pbar.length ≤ 2 ^ (i + 1) * P.length ∧
          (lvl B i).Tbar.length ≤ 2 ^ i * T.length := by sorry

end ExactPatternStream
