-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_lemma_11
-- name    : DeletionCodeRates.Levenshtein.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:21:18.510669+00:00
-- url     : https://prove2.me/theorems/7a885ac9-c6aa-43d0-be6a-0c96fea2aaab
-- title:
--   Lemma 11 — locally restricted common witnesses
-- statement:
--   Let $L\ge1$, and let $\boldsymbol c_1,\dots,\boldsymbol c_{L+1}$ be binary words starting with $0$, with repetitions allowed. If $\mathrm{LCS}(\boldsymbol c_1,\dots,\boldsymbol c_{L+1})\ge m\ge1$, there is a common subsequence $\boldsymbol w=w_1\cdots w_m$ such that $w_1=0$ is matched at position $1$ in every word and, before every subsequent match in the leftmost embeddings, at least one of the $L+1$ gaps is empty. There is no condition on the suffixes after the last match.
--
--   Differences from the source:
--   - encoding: LCS(c₁, …, c_{L+1}) ≥ m → some common subsequence v has m ≤ |v|; reason: the LCS length is the largest length of a common subsequence
--   - encoding: w₁ = 0 matched at position 1 and an empty gap before every later match → IsLocallyRestricted w c (via leftmostGaps: first gap 0 in every word; for each 1 ≤ j < m some word's gap j is 0); reason: the same condition, written with the gap lengths of the leftmost embeddings
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), Lemma 11, p. 12 (PDF 14)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RunEnsemble
import Definitions.Def_DeletionCodeRates_Levenshtein_Witness

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-- **Lemma 11** (locally restricted common witnesses, p. 12). Let `L ≥ 1` and let
`c₁, …, c_{L+1}` be binary words starting with `0`, repetitions allowed. If
`LCS(c₁, …, c_{L+1}) ≥ m ≥ 1`, there is a common subsequence `w = w₁ ⋯ w_m` with `w₁ = 0`
matched at position 1 in every word such that, before every subsequent match in the leftmost
embeddings, at least one of the `L + 1` gaps is empty. -/
theorem lemma_11 (L : ℕ) (hL : 1 ≤ L) (c : Fin (L + 1) → List (Fin 2))
    (hc : ∀ i, (c i).head? = some 0) (m : ℕ) (hm : 1 ≤ m)
    (hLCS : ∃ v : List (Fin 2), m ≤ v.length ∧ IsCommonSubseq v c) :
    ∃ w : List (Fin 2), w.length = m ∧ IsCommonSubseq w c ∧ IsLocallyRestricted w c := by sorry

end DeletionCodeRates.Levenshtein
