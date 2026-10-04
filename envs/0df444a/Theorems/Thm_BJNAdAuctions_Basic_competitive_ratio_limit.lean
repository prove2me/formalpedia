-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_competitive_ratio_limit
-- name    : BJNAdAuctions.Basic.competitive_ratio_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T16:56:39.227979+00:00
-- url     : https://prove2.me/theorems/52175dfa-e52d-4a9c-af24-e7a768f5b352
-- title:
--   Theorem 1, second sentence: the ratio tends to $1 - 1/e$ as $R_{\max} \to 0$
-- statement:
--   With $c(R) = (1+R)^{1/R}$,
--   $$
--   \lim_{R \to 0^+} \Big(1 - \frac{1}{c(R)}\Big)(1 - R) \;=\; 1 - \frac{1}{e}.
--   $$
--
--   This is the second sentence of Theorem 1: when every bid is small compared with its buyer's budget, the competitive ratio of the Allocation Algorithm approaches $1 - 1/e$.
--
--   **Formalization Note** The limit is taken along the right neighbourhood filter `𝓝[>] 0`; $1/e$ is written `Real.exp (-1)`.
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 7, Theorem 1, second sentence

import Mathlib

namespace BJNAdAuctions.Basic

open Filter Topology

/-- Theorem 1, second sentence (p. 7): as `R → 0⁺`, the competitive ratio
`(1 - 1/c)(1 - R)` with `c = (1 + R)^(1/R)` tends to `1 - 1/e`. -/
theorem competitive_ratio_limit :
    Tendsto (fun R : ℝ => (1 - 1 / (1 + R) ^ (1 / R)) * (1 - R)) (𝓝[>] 0)
      (𝓝 (1 - Real.exp (-1))) := by sorry

end BJNAdAuctions.Basic
