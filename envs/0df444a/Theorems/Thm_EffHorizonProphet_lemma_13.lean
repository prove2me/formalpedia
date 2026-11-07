-- Prove2me | Theorems.Thm_EffHorizonProphet_lemma_13
-- name    : EffHorizonProphet.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:50.588651+00:00
-- url     : https://prove2.me/theorems/b19b82b9-ce32-4950-981a-e238dfa24be4
-- title:
--   Lemma 13 — mean of the truncated geometric law
-- statement:
--   Let $S\ge1$ and $r\in[0,1)$, and let $K$ have the truncated geometric law $P(K=k)\propto r^k$ on $\{0,\dots,S-1\}$. Then
--   $$\mathbb E[K]\le\frac{r}{1-r}.$$
--
--   This is one of two elementary bounds used in the variance estimate behind Lemma 12.
--
--   Differences from the source:
--   - encoding: $\mathbb E[K]$ for a random variable $K$ → the ratio of finite sums $\sum kr^k/\sum r^k$; reason: this is the expectation under the printed law
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemma 13, p.25

import Mathlib
import Definitions.Def_EffHorizonProphet_truncGeomMoment

namespace EffHorizonProphet

/-- **Lemma 13** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.25): for `K` truncated geometric on `{0, …, S-1}` with `r ∈ [0, 1)`,
`E[K] ≤ r/(1-r)`. -/
theorem lemma_13 (S : ℕ) (hS : 1 ≤ S) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    truncGeomMoment S r 1 ≤ r / (1 - r) := by sorry

end EffHorizonProphet
