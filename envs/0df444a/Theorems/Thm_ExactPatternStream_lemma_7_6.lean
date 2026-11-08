-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_7_6
-- name    : ExactPatternStream.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:43.825896+00:00
-- url     : https://prove2.me/theorems/cda61568-d785-40ea-a1b3-d5f04c2b011c
-- title:
--   Lemma 7.6 — equal labels have weights within a factor $2$
-- statement:
--   Fix a level $0\le i\le h$ and let $u$, $v$ be node occurrences in $P_i$ and $T_i$. If $u$ and $v$ have the same label, then
--   $$\tfrac12\mathrm{wt}(\mathrm{leaves}(u))\le\mathrm{wt}(\mathrm{leaves}(v))\le2\,\mathrm{wt}(\mathrm{leaves}(u)).$$
--   Weights in a label cannot be wrong by more than a factor $2$, even under hash collisions, and this holds at all seeds.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $H_i$ sampled once level $i$ is known → one independent uniform block per level, read through a prefix (`Seeds`); reason: the same law: a prefix of an independent uniform block is uniform and independent of the lower levels
--   - encoding: "fix any injective" codes $\mathrm{code}_0$, $\mathrm{code}_{\mathrm{cnt}}$ → the fixed binary codes of `SeededHash`; reason: the source fixes one code, and nothing depends on the choice
--   - encoding: $\Sigma=\{1,\dots,|\Sigma|\}$ → `Fin σ`, shifted by one in the stream and in $f_R$; reason: the same alphabet
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.6, p.21 (PDF 22)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily
import Definitions.Def_ExactPatternStream_Counters
import Definitions.Def_ExactPatternStream_SeededHash

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.6, p.21 (PDF 22).

At any level `0 ≤ i ≤ h`, nodes `u` of `P_i` and `v` of `T_i` with the same label have `½ wt(leaves(u)) ≤ wt(leaves(v)) ≤ 2 wt(leaves(u))`, at all seeds.

**Formalization Note.** The labels are those of (14), with counters `k_cnt`. `Σ = Fin σ`. The threshold `m ≥ C` of footnote 1 is not needed. -/
theorem lemma_7_6 {σ : ℕ} (P T : List (Fin σ)) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) (ω : Seeds σ P.length) :
    let B := seededBuild P T ω
    ∀ i ≤ topIndex B, ∀ u ∈ (lvl B i).P, ∀ v ∈ (lvl B i).T, u.label = v.label →
      (wt u.leaves : ℝ) / 2 ≤ (wt v.leaves : ℝ) ∧ (wt v.leaves : ℝ) ≤ 2 * (wt u.leaves : ℝ) := by sorry

end ExactPatternStream
