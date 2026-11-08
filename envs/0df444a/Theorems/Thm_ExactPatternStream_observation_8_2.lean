-- Prove2me | Theorems.Thm_ExactPatternStream_observation_8_2
-- name    : ExactPatternStream.observation_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:14.903272+00:00
-- url     : https://prove2.me/theorems/83a7f925-d611-402d-9c49-de88b973ccd9
-- title:
--   Observation 8.2, (21) — equal leaves imply equal padded labels
-- statement:
--   For $0\le i<h$, $g_i\le p<|\hat P_i|$ and $0\le t<|\hat T_i|$,
--   $$\mathrm{leaves}(\hat P_i[p])=\mathrm{leaves}(\hat T_i[t])\implies\hat P_i[p]=\hat T_i[t].$$
--   Used in the descent of Lemma 8.4 to recover whole nodes of the padded text from leaves.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - generalization: $F_i$ of (14), fixed by §7 → an arbitrary `F` of the form (6); reason: the proof uses only that a label is a function of the labels of its group, so (14) is a special case
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Observation 8.2, eq. (21), p.24 (PDF 25)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_Candidates

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Observation 8.2, eq. (21), p.24 (PDF 25).

For `0 ≤ i < h`, `g_i ≤ p < |P̂_i|` and `0 ≤ t < |T̂_i|`: `leaves(P̂_i[p]) = leaves(T̂_i[t])` implies `P̂_i[p] = T̂_i[t]`, for every choice of the hash functions.

**Formalization Note.** The conclusion compares labels. -/
theorem observation_8_2 (F : GroupHash) (P T : List ℕ) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) :
    let B := build F P T
    ∀ i < topIndex B, ∀ p t : ℕ, (lvl B i).g ≤ p → p < (lvl B i).hatPt.length →
      t < (lvl B i).hatTt.length →
      ((lvl B i).hatPt.getD p default).leaves = ((lvl B i).hatTt.getD t default).leaves →
      (lvl B i).hatP.getD p default = (lvl B i).hatT.getD t default := by sorry

end ExactPatternStream
