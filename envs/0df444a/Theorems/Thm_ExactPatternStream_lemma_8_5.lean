-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_8_5
-- name    : ExactPatternStream.lemma_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:44.663672+00:00
-- url     : https://prove2.me/theorems/069ce76f-6bad-4872-ae6b-286c8d163281
-- title:
--   Lemma 8.5 — soundness: $\Pr[M\not\subseteq\mathrm{Occ}(P,T)]\le(\log m)^{-2}$
-- statement:
--   Let $M$ be the output of Algorithm 2. Then for all sufficiently large $m$,
--   $$\Pr[M\not\subseteq\mathrm{Occ}(P,T)]\le(\log m)^{-2}.$$
--   This, with Lemma 5.2, gives all the correctness of the algorithm, separately from its implementation.
--
--   Differences from the source:
--   - encoding: "for all sufficiently large $m$", $|\Sigma|\le n^{O(1)}$ → $\forall k\,\exists C$: $m\ge C$ and $\sigma\le n^k$; reason: $|\Sigma|\le n^{O(1)}$ means every polynomial bound
--   - reading: $\log m$ → $\log_2m$; reason: the stronger reading among bases $\ge2$, and the base of §7
--   - encoding: $M$ a set of positions → $M$ a `Finset ℤ`, and $\mathrm{Occ}$ cast to `ℤ`; reason: a negative candidate must count as an error
--   - generalization: "Choose a prime $p_R>2^{4\mathcal L}$ with $\log p_R=O(\log m)$" → every prime $p_R>2^{4\mathcal L}$; reason: the bound on $\log p_R$ is used only for space (decision 9), and the source choice is included
--   - encoding: $H_i$ sampled once level $i$ is known → one independent uniform block per level, read through a prefix (`Seeds`); reason: the same law: a prefix of an independent uniform block is uniform and independent of the lower levels
--   - encoding: "fix any injective" codes $\mathrm{code}_0$, $\mathrm{code}_{\mathrm{cnt}}$ → the fixed binary codes of `SeededHash`; reason: the source fixes one code, and nothing depends on the choice
--   - encoding: $\Sigma=\{1,\dots,|\Sigma|\}$ → `Fin σ`, shifted by one in the stream and in $f_R$; reason: the same alphabet
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 8.5, p.26 (PDF 27)

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

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 8.5, p.26 (PDF 27).

Soundness: let `M` be the output of Algorithm 2. For all sufficiently large `m`, `Pr[M ⊄ Occ(P, T)] ≤ (log m)^{-2}`.

**Formalization Note.** "Sufficiently large" is `∀ k, ∃ C` with `|Σ| ≤ n^k`, the paper's `|Σ| ≤ n^{O(1)}`. The probability is over the recursive seeds and an independent uniform `a_R`, for every prime `p_R > 2^{4𝓛}`. `P, T` are fixed before the seeds. `M` is a set of integers, so a negative candidate counts as an error. `log = log₂`. -/
theorem lemma_8_5 : ∀ k : ℕ, ∃ C : ℕ, ∀ (σ : ℕ) (P T : List (Fin σ)) (pR : ℕ) [Fact pR.Prime],
    C ≤ P.length → P.length ≤ T.length → T.length ≤ 2 * P.length → σ ≤ T.length ^ k →
    2 ^ (4 * bigL σ P.length) < pR →
    unifProb (fun s : Seeds σ P.length × ZMod pR => ¬ seededMatch P T s ⊆ occZ P T) ≤
      ((Real.logb 2 P.length) ^ 2)⁻¹ := by sorry

end ExactPatternStream
