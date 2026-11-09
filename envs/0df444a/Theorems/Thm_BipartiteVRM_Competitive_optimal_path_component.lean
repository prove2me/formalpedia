-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_optimal_path_component
-- name    : BipartiteVRM.Competitive.optimal_path_component
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:14.48211+00:00
-- url     : https://prove2.me/theorems/d2185fec-adbc-44f4-af13-7fc77e96798e
-- title:
--   §4.2 — the defined optimal walk is the whole alternating component
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, any TA-optimal perfect matching $M^*$, a time $t\ge0$, and a free request $r$. The defined walk $P_r^*(t)$ is the full component of $M_t\mathbin{\triangle}M^*$ containing $r$:
--
--   $$P_r^*(t)\text{ is an }M_t\text{-augmenting path from }r\text{ to an }M_t\text{-free server},$$
--
--   and its edges are exactly all edges in that connected component. The terminal server may not yet have arrived; the carrier here is the full finite input rather than the arrived graph. This verifies that the finite walk definition is not a truncated path or an arbitrary path chosen for the analysis. It is the unnumbered defining observation in §4.2, not an invented source lemma.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the path component of M_t symmetric-difference Mstar containing a free request → the ordered walk which follows an Mstar edge forward and an M_t edge backward, with an analysis bound of size plus one iterations; reason: optimal_path_component concludes that this computes the whole component; the terminal server need not have arrived
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 10, §4.2, paragraph defining the optimal path before Lemma 4.2

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- §4.2, p. 10, the paragraph defining P*_r(t). The walk computes the whole
component, including a possibly unarrived terminal server; the fuel does not truncate it. -/
theorem optimal_path_component {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching)
    (hMstar : IsOptimal I Mstar) (t : ℝ) (ht : 0 ≤ t) (r : ℕ)
    (hr : r ∈ freeAt I γ tie t) :
    SymmetricDifferencePath I.items (stateAt I γ tie t).off Mstar r
      (optimalPath I γ tie Mstar t r) := by sorry

end BipartiteVRM.Competitive
