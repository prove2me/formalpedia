-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_8_4
-- name    : ExactPatternStream.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:17.527442+00:00
-- url     : https://prove2.me/theorems/f1b7f6f6-c4dc-4464-b054-c5ea2b67e842
-- title:
--   Lemma 8.4 — one step of the descent
-- statement:
--   Let $0\le i<h$ and $x_{i+1}\in M_{i+1}$. If (20) holds at $(r,x)=(i+1,x_{i+1})$, then, for $x_i=\mathrm{jump}_i^{-1}(x_{i+1})$,
--   $$x_i\in M_i\quad\text{and}\quad\gamma_i(e_i(x_i))=\gamma_{i+1}(e_{i+1}(x_{i+1})).$$
--   A candidate at level $i+1$ thereby descends to a candidate at level $i$ with the same raw endpoint, and at level $0$ a candidate is a true occurrence.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - generalization: $F_i$ of (14), fixed by §7 → an arbitrary `F` of the form (6); reason: the proof uses only that a label is a function of the labels of its group, so (14) is a special case
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
--   - encoding: $x_i=\mathrm{jump}_i^{-1}(x_{i+1})$ → a preimage in $U^{(T)}_i$ exists and every preimage has the two properties; reason: $\mathrm{jump}_i$ is a bijection on $U^{(T)}_i$ (p.11), so this is the same statement
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 8.4, p.24 (PDF 25)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_Candidates

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 8.4, p.24 (PDF 25).

Let `0 ≤ i < h` and `x_{i+1} ∈ M_{i+1}`. If (20) holds at `(i + 1, x_{i+1})`, then for `x_i = jump_i^{-1}(x_{i+1})`, `x_i ∈ M_i` and `γ_i(e_i(x_i)) = γ_{i+1}(e_{i+1}(x_{i+1}))`.

**Formalization Note.** Holds for every choice of the hash functions. `jump_i^{-1}` is spelled out: a preimage in `U^(T)_i` exists (p.22), and every preimage has the two properties. -/
theorem lemma_8_4 (F : GroupHash) (P T : List ℕ) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) :
    let B := build F P T
    ∀ i < topIndex B, ∀ y ∈ (lvl B (i + 1)).Mi, Implication20 (lvl B i) (lvl B (i + 1)) y →
      (∃ x ∈ (lvl B i).UT, (lvl B i).jump x = y) ∧
      ∀ x ∈ (lvl B i).UT, (lvl B i).jump x = y →
        x ∈ (lvl B i).Mi ∧
          (lvl B i).γ ((lvl B i).e x) = (lvl B (i + 1)).γ ((lvl B (i + 1)).e y) := by sorry

end ExactPatternStream
