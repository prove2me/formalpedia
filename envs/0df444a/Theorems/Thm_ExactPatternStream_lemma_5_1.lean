-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_5_1
-- name    : ExactPatternStream.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:33.442682+00:00
-- url     : https://prove2.me/theorems/c4f1c443-b867-4597-a52f-29f66137592f
-- title:
--   Lemma 5.1 — exact occurrences go up the trees
-- statement:
--   For every $0\le i<h$, $O_i\subseteq U^{(T)}_i$ and $\mathrm{jump}_i(O_i)\subseteq O_{i+1}$, for every choice of the hash functions. Here $O_i$ is the set of active positions of $T_i$ whose annotated forest equals that of $P_i[1\,.\,.\,m_i]$.
--
--   It tracks a true occurrence from level $0$ to the top level, and it is the core of completeness.
--
--   **Formalization Note** Forests are lists of `ParseTree`, retaining labels and annotations.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $F_i$ of the form (6), "specified in Section 7.3" → an arbitrary argument `F`, with values $(y,z,\alpha)$; reason: §§4–5 of the source are written for any such $F_i$, and (14) is one
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 5.1, p.13 (PDF 14)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 5.1, p.13 (PDF 14).

Exact occurrences of the annotated forests go up the trees: for every `0 ≤ i < h`, `O_i ⊆ U^(T)_i` and `jump_i(O_i) ⊆ O_{i+1}`, for every choice of the hash functions.

**Formalization Note.** `O_i` is `occSet`: forests are compared as lists of `ParseTree`, which retain every label and annotation. -/
theorem lemma_5_1 (F : GroupHash) (P T : List ℕ) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) :
    let B := build F P T
    ∀ i < topIndex B,
      (∀ x ∈ occSet (lvl B i), x ∈ (lvl B i).UT) ∧
        ∀ x ∈ occSet (lvl B i), (lvl B i).jump x ∈ occSet (lvl B (i + 1)) := by sorry

end ExactPatternStream
