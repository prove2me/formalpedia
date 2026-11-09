-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_2_5
-- name    : BLTCounting.AccuracySpace.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:21.036402+00:00
-- url     : https://prove2.me/theorems/67dd921f-fa62-4c5a-86da-f876677ea353
-- title:
--   Bounded recurrence implies low Hankel rank
-- statement:
--   Let $c$ be a BLT sequence of recurrence order $d$. Then for every $m\ge1$ the $m\times m$ Hankel matrix $H_m(c)[r,s]=c[r+s]$ satisfies
--   $$\mathrm{rank}\,H_m(c)\le d.$$
--   This is the link from memory to linear algebra: a small recurrence order forces a low-rank Hankel matrix.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 2.5, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix

namespace BLTCounting.AccuracySpace

/-- Lemma 2.5, PDF p. 11: a sequence with a constant-coefficient recurrence of order at most `d`
(equation (3)) has `rank(H_m(c)) ≤ d` for every `m ≥ 1`. -/
theorem lemma_2_5 {d : ℕ} {c : ℕ → ℂ} (hc : IsBLT d c) (m : ℕ) (hm : 1 ≤ m) :
    (hankel m c).rank ≤ d := by sorry

end BLTCounting.AccuracySpace
