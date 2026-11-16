-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_lemma_3_1
-- name    : BLTCounting.AccuracySpace.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:53.363885+00:00
-- url     : https://prove2.me/theorems/ab4eed0a-e54d-4860-8e9d-b846c87ff961
-- title:
--   Lemma 3.1 — Hankel error and singular-value count
-- statement:
--   Let $n,d\ge1$, let $c$ be a complex sequence, put $m=\lfloor(n+1)/2\rfloor$ and let $f[k]=4^{-k}\binom{2k}{k}$. If $\|c-f\|_{\ell_2(0,n-1)}\le\eta$ and $\operatorname{rank}H_m(c)\le d$, then
--   $$d\ge\#\{j:s_j(H_m(f))>\eta\sqrt m\}.$$
--   The norm is unnormalized and forces $\eta\ge0$. This reduces finite coefficient approximation to a singular-value count.
--
--   Differences from the source:
--   - encoding: finite coefficient squared-error bound with its nonnegative error convention → the equivalent unnormalized norm bound; reason: the norm enforces the inherited nonnegative η and retains the exact threshold
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.1, printed p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Lemma 3.1, PDF p.13. The norm hypothesis includes η ≥ 0, unlike a signed squared-error bound. -/
theorem lemma_3_1 (n d : ℕ) (hn : 1 ≤ n) (hd : 0 < d) (c : ℕ → ℂ) (η : ℝ)
    (herr : coeffErr n c sqrtSeq ≤ η)
    (hrank : (hankel ((n + 1) / 2) c).rank ≤ d) :
    singularCountAbove (hankel ((n + 1) / 2) sqrtSeq)
      (η * Real.sqrt (((n + 1) / 2 : ℕ) : ℝ)) ≤ d := by sorry

end BLTCounting.AccuracySpace.Supplement
