-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_7_7
-- name    : ExactPatternStream.lemma_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:54.225747+00:00
-- url     : https://prove2.me/theorems/0e399e7a-7090-489f-908c-5641ecac0363
-- title:
--   Lemma 7.7 — the residual test is reliable with probability $1-2^{-\mathcal L}$
-- statement:
--   With probability at least $1-2^{-\mathcal L}$, every residual string tested by Algorithm 2 that passes (16), i.e. $f_R(Z)=f_R(R')$, equals $R'$.
--
--   The Karp–Rabin fingerprint on the residual is needed only at the last level, so a single long fingerprint suffices.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - generalization: "Choose a prime $p_R>2^{4\mathcal L}$ with $\log p_R=O(\log m)$" → every prime $p_R>2^{4\mathcal L}$; reason: the bound on $\log p_R$ is used only for space (decision 9), and the source choice is included
--   - encoding: $H_i$ sampled once level $i$ is known → one independent uniform block per level, read through a prefix (`Seeds`); reason: the same law: a prefix of an independent uniform block is uniform and independent of the lower levels
--   - encoding: "fix any injective" codes $\mathrm{code}_0$, $\mathrm{code}_{\mathrm{cnt}}$ → the fixed binary codes of `SeededHash`; reason: the source fixes one code, and nothing depends on the choice
--   - encoding: $\Sigma=\{1,\dots,|\Sigma|\}$ → `Fin σ`, shifted by one in the stream and in $f_R$; reason: the same alphabet
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.7, p.22 (PDF 23)

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

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.7, p.22 (PDF 23).

With probability at least `1 - 2^{-𝓛}`, every residual string tested by Algorithm 2 that passes (16) equals `R'`.

**Formalization Note.** The probability is over the recursive seeds and an independent uniform `a_R`, for every prime `p_R > 2^{4𝓛}` (p.22; the bound on `log p_R` is only for space). A tested string is that of an index `k ∈ [0 . . |T_h|]` passing the loop condition of Algorithm 2. The threshold `m ≥ C` of footnote 1 is not needed. -/
theorem lemma_7_7 {σ : ℕ} (pR : ℕ) [Fact pR.Prime] (P T : List (Fin σ)) (hm : 1 ≤ P.length)
    (hmn : P.length ≤ T.length) (hn : T.length ≤ 2 * P.length)
    (hp : 2 ^ (4 * bigL σ P.length) < pR) :
    1 - (2 : ℝ)⁻¹ ^ bigL σ P.length ≤
      unifProb (fun s : Seeds σ P.length × ZMod pR =>
        let B := seededBuild P T s.1
        let L := lvl B (topIndex B)
        ∀ k ≤ L.T.length, L.AT.getD k false = true →
          slice (labels L.T) k (k + L.c) = slice (labels L.P) 1 (L.c + 1) →
          fR s.2 (L.scan k) = fR s.2 L.Res → L.scan k = L.Res) := by sorry

end ExactPatternStream
