-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_charging_identities
-- name    : BipartiteVRM.Competitive.charging_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:28.641707+00:00
-- url     : https://prove2.me/theorems/af0eb3bc-4fb2-498e-976b-c16e2ce160ac
-- title:
--   Equations (4.1) and (4.4) — finite integrals and exact charge conservation
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, and any TA-optimal perfect matching $M^*$. The actual Case 1 rate, all Case 2 edge rates, and the number of free requests are integrable on the nonnegative time axis. The charge rates are nonnegative and satisfy the exact identities
--
--   $$W_R=\int_0^\infty |R_{\rm free}(t)|\,dt
--   =W_1+\sum_{e\in M^*}\int_0^\infty q_e(t)\,dt.$$
--
--   All quantities come from the explicit execution and the source's charging rules. Integrability is a conclusion, not a hypothesis; event times receive zero charge and form a finite set. This preserves the two unnumbered source identities needed to combine the eight numbered lemmas. It is not an additional numbered milestone.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the path component of M_t symmetric-difference Mstar containing a free request → the ordered walk which follows an Mstar edge forward and an M_t edge backward, with an analysis bound of size plus one iterations; reason: optimal_path_component concludes that this computes the whole component; the terminal server need not have arrived
--   - encoding: nonnegative waiting charges integrated from zero to infinity → the ENNReal Lebesgue integrals of the actual nonnegative rates on the nonnegative real half-line; reason: extended nonnegative integration has no nonintegrable-equals-zero default; charging_identities separately concludes integrability and the exact waiting identities
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 9, (4.1); pp. 10–11, §4.2, (4.3)–(4.4)

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

open MeasureTheory

/-- (4.1), (4.3), (4.4), pp. 9–11, with the measurability/finiteness facts
needed for their literal integral meaning. There is no integrability hypothesis. -/
theorem charging_identities {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching)
    (hMstar : IsOptimal I Mstar) :
    IntegrableOn (caseOneRate I γ tie Mstar) (Set.Ici (0 : ℝ)) ∧
    (∀ e ∈ Mstar, IntegrableOn (chargeRate I γ tie Mstar e) (Set.Ici (0 : ℝ))) ∧
    IntegrableOn (fun t => ((freeAt I γ tie t).card : ℝ)) (Set.Ici (0 : ℝ)) ∧
    (∀ t, 0 ≤ caseOneRate I γ tie Mstar t) ∧
    (∀ e ∈ Mstar, ∀ t, 0 ≤ chargeRate I γ tie Mstar e t) ∧
    ENNReal.ofReal (requestWaiting I γ tie) =
      ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal ((freeAt I γ tie t).card : ℝ) ∧
    ENNReal.ofReal (requestWaiting I γ tie) =
      Wone I γ tie Mstar + ∑ e ∈ Mstar, edgeCharge I γ tie Mstar e := by sorry

end BipartiteVRM.Competitive
