-- Prove2me | Theorems.Thm_ExactPatternStream_observation_8_3
-- name    : ExactPatternStream.observation_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:11.291934+00:00
-- url     : https://prove2.me/theorems/f7463050-e280-4112-bb57-cc15ced61b4b
-- title:
--   Observation 8.3, (22) — a nonempty residual starts with a character
-- statement:
--   For every $0\le i\le h$,
--   $$\mathrm{Res}_i\ne\varepsilon\implies\mathrm{Res}_i[0]\in\Sigma.$$
--   So a residual cannot start inside padding, which fixes its endpoint in the descent of Lemma 8.4.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - generalization: $F_i$ of (14), fixed by §7 → an arbitrary `F` of the form (6); reason: the proof uses only that a label is a function of the labels of its group, so (14) is a special case
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Observation 8.3, eq. (22), p.24 (PDF 25)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_Candidates

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Observation 8.3, eq. (22), p.24 (PDF 25).

For every `0 ≤ i ≤ h`, `Res_i ≠ ε` implies `Res_i[0] ∈ Σ`, for every choice of the hash functions. -/
theorem observation_8_3 (F : GroupHash) (P T : List ℕ) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) :
    let B := build F P T
    ∀ i ≤ topIndex B, (lvl B i).Res ≠ [] → ∃ a, (lvl B i).Res.head? = some (Leaf.sym a) := by sorry

end ExactPatternStream
