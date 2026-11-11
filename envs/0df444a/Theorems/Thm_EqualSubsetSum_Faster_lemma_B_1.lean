-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_B_1
-- name    : EqualSubsetSum.Faster.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:23:44.969359+00:00
-- url     : https://prove2.me/theorems/e3442487-9f7b-4636-9a63-1571ad2bb7a2
-- title:
--   Lemma B.1 — C is continuous and increasing on [1/9, 1/3], attained with T(p,q) = C(p)
-- statement:
--   The function
--   $$C(p)=\min_{0\le q\le(1-p)/2}\max\{H(p)+q,\ (1-p)[1-H(q/(1-p))]\}$$
--   is continuous and increasing on $[1/9,1/3]$. For every $p$ in this interval there is a minimizing $q\in[0,(1-p)/2]$ with $T(p,q)=C(p)$.
--
--   It shows the step-two procedure attains exponent $C(p)$, half-list generation included.
--
--   Differences from the source:
--   - reading: C is increasing → StrictMonoOn (strictly increasing); reason: the proof shows C′ > 0 and C = H strictly increasing in the q = 0 regime; the strict reading is the stronger one
--   - encoding: min over 0 ≤ q ≤ (1−p)/2 → sInf of the values on the interval, together with the stated existence of a minimizing q attaining it; reason: the minimizer clause of the lemma asserts attainment explicitly
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 53, Lemma B.1

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Exponents

namespace EqualSubsetSum.Faster

/-- Lemma B.1 (p. 53). `C` is continuous and increasing on `[1/9, 1/3]`, and for every `p` in this
interval there is a minimizing `q ∈ [0, (1-p)/2]` with `T(p, q) = C(p)`. -/
theorem lemma_B_1 :
    ContinuousOn Cstep (Set.Icc (1 / 9) (1 / 3)) ∧
    StrictMonoOn Cstep (Set.Icc (1 / 9) (1 / 3)) ∧
    ∀ p ∈ Set.Icc (1 / 9 : ℝ) (1 / 3), ∃ q ∈ Set.Icc (0 : ℝ) ((1 - p) / 2),
      stepTwoObjective p q = Cstep p ∧ Tstep p q = Cstep p := by sorry

end EqualSubsetSum.Faster
