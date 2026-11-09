-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_4_1
-- name    : BLTCounting.AccuracySpace.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:23.646903+00:00
-- url     : https://prove2.me/theorems/d860e7e3-9f42-4b50-bf95-36de0b85807c
-- title:
--   Weighted coefficient-error reduction
-- statement:
--   Let $m\ge4$ and $S\subseteq\{1,\dots,m-1\}$, possibly empty, and let $\widehat H_S(e)$ be the weighted Hankel matrix of a complex sequence $e$. Then
--   $$\|\widehat H_S(e)\|_2^2\le\|\widehat H_S(e)\|_F^2\le4\sum_{k=0}^{2m-2}|e[k]|^2.$$
--   The weights make the multiplicity of each coefficient bounded by an absolute constant, so a small coefficient error gives a small matrix error with no dependence on $m$.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 4.1, printed p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix

namespace BLTCounting.AccuracySpace

/-- Lemma 4.1, PDF p. 25: for `m ≥ 4`, `S ⊆ {1, …, m-1}` (possibly empty) and every complex sequence `e`,
`‖Ĥ_S(e)‖₂² ≤ ‖Ĥ_S(e)‖_F² ≤ 4 ∑_{k=0}^{2m-2} |e[k]|²`. -/
theorem lemma_4_1 (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 m) (e : ℕ → ℂ) :
    specNorm (weightedHankel S e) ^ 2 ≤ frobNorm (weightedHankel S e) ^ 2 ∧
      frobNorm (weightedHankel S e) ^ 2 ≤
        4 * ∑ k ∈ Finset.range (2 * m - 1), ‖e k‖ ^ 2 := by sorry

end BLTCounting.AccuracySpace
