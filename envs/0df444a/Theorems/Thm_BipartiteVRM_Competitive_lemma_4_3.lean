-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_4_3
-- name    : BipartiteVRM.Competitive.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:27.465973+00:00
-- url     : https://prove2.me/theorems/659118cd-8a30-4236-9827-c8a759111bb0
-- title:
--   Lemma 4.3 — total Case 1 waiting charge
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, and any TA-optimal perfect matching $M^*$. Let $W_1$ be the integral of the actual Case 1 rates: at stable times, each free request whose optimal path ends at an unarrived server charges its full unit waiting rate to that path's last edge. Then
--
--   $$W_1\le\mathrm{OPT}.$$
--
--   The charges are computed from the execution and the fixed comparison matching. This bounds the part of request waiting caused by unarrived terminal servers, including zero-optimum and empty inputs.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the path component of M_t symmetric-difference Mstar containing a free request → the ordered walk which follows an Mstar edge forward and an M_t edge backward, with an analysis bound of size plus one iterations; reason: optimal_path_component concludes that this computes the whole component; the terminal server need not have arrived
--   - encoding: nonnegative waiting charges integrated from zero to infinity → the ENNReal Lebesgue integrals of the actual nonnegative rates on the nonnegative real half-line; reason: extended nonnegative integration has no nonintegrable-equals-zero default; charging_identities separately concludes integrability and the exact waiting identities
--   - encoding: the minimum actual distance-plus-both-sides-delay objective OPT in (2.1) → the real projection of its ENNReal infimum over every perfect matching and feasible real match-time function; reason: offline_attainment and the main goal conclude finiteness and attainment, so the projection never substitutes a default for an infinite value
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 11, Lemma 4.3; pp. 10–11, §4.2 charging scheme

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 4.3, p. 11: the integrated actual Case 1 charges, not a free scalar W₁. -/
theorem lemma_4_3 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching)
    (hMstar : IsOptimal I Mstar) :
    Wone I γ tie Mstar ≤ ENNReal.ofReal (OPT I) := by sorry

end BipartiteVRM.Competitive
