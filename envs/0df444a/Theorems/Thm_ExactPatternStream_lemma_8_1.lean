-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_8_1
-- name    : ExactPatternStream.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:12.930203+00:00
-- url     : https://prove2.me/theorems/bd79c959-82a4-4e4b-831b-b63658dd9d0f
-- title:
--   Lemma 8.1 — the implication (20) holds with probability $1-O(\mathcal L^42^{-b/2})$
-- statement:
--   With probability at least $1-O(\mathcal L^42^{-b/2})$ over the recursive seeds, the implication (20) holds simultaneously, for every $1\le r\le h$:
--
--   1. at every $x\in A_r\cap W_r$; and
--   2. if some level $j<r$ is heavy, at every $x\in A_r$.
--
--   Here $\tau=m/(4\mathcal L)$. This restricts the comparisons to few text blocks, which is what Lemma 7.4 can pay for.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $H_i$ sampled once level $i$ is known → one independent uniform block per level, read through a prefix (`Seeds`); reason: the same law: a prefix of an independent uniform block is uniform and independent of the lower levels
--   - encoding: "fix any injective" codes $\mathrm{code}_0$, $\mathrm{code}_{\mathrm{cnt}}$ → the fixed binary codes of `SeededHash`; reason: the source fixes one code, and nothing depends on the choice
--   - encoding: $\Sigma=\{1,\dots,|\Sigma|\}$ → `Fin σ`, shifted by one in the stream and in $f_R$; reason: the same alphabet
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 8.1, p.23 (PDF 24)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily
import Definitions.Def_ExactPatternStream_Counters
import Definitions.Def_ExactPatternStream_SeededHash
import Definitions.Def_ExactPatternStream_Candidates

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 8.1, p.23 (PDF 24).

With probability at least `1 - O(𝓛⁴ 2^{-b/2})`, the implication (20) holds simultaneously, for every `1 ≤ r ≤ h`, (i) at every `x ∈ A_r ∩ W_r`, and (ii) if some level `j < r` is heavy, at every `x ∈ A_r`.

**Formalization Note.** The probability is over the recursive seeds, one independent uniform block per level. `τ = m/(4𝓛)`. `O(·)` is one absolute `K` before all variables; `b` is the integer `16⌈log₂ 𝓛⌉`, and `2^{-b/2}` is the real power. The threshold `m ≥ C` of footnote 1 is not needed. -/
theorem lemma_8_1 : ∃ K : ℝ, ∀ (σ : ℕ) (P T : List (Fin σ)), 1 ≤ P.length → P.length ≤ T.length →
    T.length ≤ 2 * P.length →
    let τ : ℝ := (P.length : ℝ) / (4 * (bigL σ P.length : ℝ))
    1 - K * (bigL σ P.length : ℝ) ^ 4 / (2 : ℝ) ^ ((hashB σ P.length : ℝ) / 2) ≤
      unifProb (fun ω : Seeds σ P.length =>
        let B := seededBuild P T ω
        ∀ r : ℕ, 1 ≤ r → r ≤ topIndex B →
          (∀ x ∈ (lvl B r).Ai ∩ (lvl B r).Wi τ, Implication20 (lvl B (r - 1)) (lvl B r) x) ∧
          ((∃ j < r, (lvl B j).IsHeavy τ) →
            ∀ x ∈ (lvl B r).Ai, Implication20 (lvl B (r - 1)) (lvl B r) x)) := by sorry

end ExactPatternStream
