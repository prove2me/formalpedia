-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_4_1
-- name    : BipartiteVRM.Competitive.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:04.084338+00:00
-- url     : https://prove2.me/theorems/ac085e9e-5a3d-4443-84f8-d7f481ed1b19
-- title:
--   Lemma 4.1 — total algorithm cost versus request waiting
-- statement:
--   Let $\gamma>1$ and fix any causal deterministic tie rule. Write $\mathrm{ALG}$ for the cost of the actual VRM output, including distances and the waiting times of both requests and servers. Write $W_R=\sum_r(t_r-a_r)$ for the waiting times of requests alone. Then
--
--   $$\mathrm{ALG}\le\left(2+\frac{2\gamma}{\gamma-1}\right)W_R.$$
--
--   This reduces the total cost comparison to the request waiting quantity used in §4.2. Both quantities are computed from the explicit execution. The empty input and zero costs remain included.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 9, Lemma 4.1; pp. 9–10, §4.1, (4.1)–(4.2)

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 4.1, p. 9: ALG includes both sides' delays, while W_R includes requests only. -/
theorem lemma_4_1 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) :
    ALG I γ tie ≤ (2 + 2 * γ / (γ - 1)) * requestWaiting I γ tie := by sorry

end BipartiteVRM.Competitive
