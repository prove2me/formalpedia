-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_lemma2a_normal_tail
-- name    : FedergruenZipkin.AvgCost.lemma2a_normal_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:18:56.8797+00:00
-- url     : https://prove2.me/theorems/4cb19dd8-5167-4ded-9635-7f8b6bfaecfb
-- title:
--   Lemma 2(a) (p. 196) — $1-\Phi(z) < e^{-z/2}$ for $z \ge 0$
-- statement:
--   Let $\Phi$ be the standard normal cumulative distribution function. For every real $z \ge 0$,
--   $$1 - \Phi(z) < \exp\bigl(-\tfrac12 z\bigr).$$
--
--   This elementary tail estimate is used in the proof of Lemma 3 to bound the probability that the cumulative demand exceeds its mean by a large amount.
--
--   **Formalization Note** The exponent is $-\tfrac12 z$ as printed (not $-\tfrac12 z^2$); the inequality holds as printed. $\Phi$ is the cdf of Mathlib's `gaussianReal 0 1`.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 196, Lemma 2(a)

import Mathlib

namespace FedergruenZipkin.AvgCost
theorem lemma2a_normal_tail (z : ℝ) (hz : 0 ≤ z) :
    1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) z < Real.exp (-(1 / 2) * z) := by sorry
end FedergruenZipkin.AvgCost
