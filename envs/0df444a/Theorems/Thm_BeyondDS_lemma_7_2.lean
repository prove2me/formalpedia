-- Prove2me | Theorems.Thm_BeyondDS_lemma_7_2
-- name    : BeyondDS.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:48.5642+00:00
-- url     : https://prove2.me/theorems/3acda17c-d4dc-4c1c-a4a2-54d8037b13a4
-- title:
--   Lemma 7.2 — $\Pr[D_U<K/16]\le e^{-K/128}$ for $|U|\ge n/4$
-- statement:
--   Let $U\subseteq[n]$ with $|U|\ge n/4$ and let $1\le K\le n$. For $K$ independent uniform destinations in $[n]$, the number $D_U$ of distinct destinations in $U$ satisfies
--
--   $$\Pr[D_U<K/16]\le e^{-K/128}.$$
--
--   It is the occupancy estimate behind the uniform sampler (Lemma 7.3) and the second case of Lemma 7.5.
--
--   Differences from the source:
--
--   - encoding: K independent uniform destinations → the uniform law on maps Fin K → Fin n; reason: same law
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Lemma 7.2, p.23 (PDF p.24), eq. (11)

import Mathlib
import Definitions.Def_BeyondDS_TrialStep

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS

/-- Lemma 7.2 (Distinct destinations), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.23 (PDF 24), eq. (11): for `U ⊆ [n]` with `|U| ≥ n/4` and
`1 ≤ K ≤ n`, among `K` independent uniform destinations the number `D_U` of distinct destinations in `U` satisfies
`Pr[D_U < K/16] ≤ exp(−K/128)`. The comparison is in the reals. -/
theorem lemma_7_2 (n K : ℕ) [NeZero n] (U : Finset (Fin n)) (hU : (n : ℝ) / 4 ≤ U.card) (hK₁ : 1 ≤ K) (hKn : K ≤ n) :
    (PMF.uniformOfFintype (Fin K → Fin n)).toOuterMeasure {f | (distinctIn f U : ℝ) < (K : ℝ) / 16} ≤
      ENNReal.ofReal (Real.exp (-((K : ℝ) / 128))) := by sorry

end BeyondDS
