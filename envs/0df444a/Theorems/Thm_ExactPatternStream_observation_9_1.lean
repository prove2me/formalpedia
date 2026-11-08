-- Prove2me | Theorems.Thm_ExactPatternStream_observation_9_1
-- name    : ExactPatternStream.observation_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:33.195236+00:00
-- url     : https://prove2.me/theorems/20888ca7-0245-4354-8cf1-f3f6a35526bb
-- title:
--   Observation 9.1 — $A^{(S)}_i[x]=\alpha(S_i[x-1])$
-- statement:
--   For every $0\le i\le h$, $S\in\{P,T\}$ and $1\le x\le|S_i|$,
--   $$A^{(S)}_i[x]=\alpha(S_i[x-1]).$$
--   So annotations can be read off the preceding label and need not be stored separately in a stream.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $H_i$ sampled once level $i$ is known → one independent uniform block per level, read through a prefix (`Seeds`); reason: the same law: a prefix of an independent uniform block is uniform and independent of the lower levels
--   - encoding: "fix any injective" codes $\mathrm{code}_0$, $\mathrm{code}_{\mathrm{cnt}}$ → the fixed binary codes of `SeededHash`; reason: the source fixes one code, and nothing depends on the choice
--   - encoding: $\Sigma=\{1,\dots,|\Sigma|\}$ → `Fin σ`, shifted by one in the stream and in $f_R$; reason: the same alphabet
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Observation 9.1, p.27 (PDF 28)

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

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Observation 9.1, p.27 (PDF 28).

For every `0 ≤ i ≤ h`, `S ∈ {P, T}` and `1 ≤ x ≤ |S_i|`, `A^(S)_i[x] = α(S_i[x - 1])`, at all seeds.

**Formalization Note.** Only the coordinate `α_i` of (14) is used, and it is part of `seededF`. The threshold `m ≥ C` of footnote 1 is not needed. -/
theorem observation_9_1 {σ : ℕ} (P T : List (Fin σ)) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) (ω : Seeds σ P.length) :
    let B := seededBuild P T ω
    ∀ i ≤ topIndex B,
      (∀ x : ℕ, 1 ≤ x → x ≤ (lvl B i).P.length →
        (lvl B i).AP.getD x false = alphaOf ((labels (lvl B i).P).getD (x - 1) default)) ∧
      ∀ x : ℕ, 1 ≤ x → x ≤ (lvl B i).T.length →
        (lvl B i).AT.getD x false = alphaOf ((labels (lvl B i).T).getD (x - 1) default) := by sorry

end ExactPatternStream
